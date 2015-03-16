#include "secure_storage.h"

#include "stdlib.h"
#include "string.h"

//@ #include "quantifiers.gh"

#define APP_RECEIVE_PORT 121212

void app_send(char *key, int key_len, char *message, int message_len)
  /*@ requires [?f0]polarssl_world(ss_polarssl_pub) &*&
               [?f1]polarssl_cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
                 key_cg == polarssl_symmetric_key(?creator, ?id) &*&
               [?f2]polarssl_public_message(ss_polarssl_pub)
                                           (message, message_len, ?msg_cs) &*&
                 message_len >= POLARSSL_MIN_HMAC_INPUT_BYTE_SIZE &*&
                 message_len < POLARSSL_MAX_MESSAGE_BYTE_SIZE - 64 &*&
               app_send_event(creator, msg_cs) == true;
  @*/
  /*@ ensures  [f0]polarssl_world(ss_polarssl_pub) &*&
               [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg) &*&
               [f2]polarssl_public_message(ss_polarssl_pub)
                                          (message, message_len, msg_cs);
  @*/
{
  int socket;
  char hmac[64];
  
  net_usleep(20000);
  if(net_connect(&socket, NULL, APP_RECEIVE_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();

  //@ open [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg);
  //@ close polarssl_key_id(creator, id);
  /*@ open [f2]polarssl_public_message(ss_polarssl_pub)
                                      (message, message_len, msg_cs); @*/
  sha512_hmac(key, (unsigned int) key_len, message, 
              (unsigned int) message_len, hmac, 0);
  //@ assert polarssl_cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
  //@ close ss_polarssl_pub(hmac_cg);
  //@ leak ss_polarssl_pub(hmac_cg);
  /*@ polarssl_public_message_from_cryptogram(
                               ss_polarssl_pub, hmac, 64, hmac_cs, hmac_cg); @*/
  //@ open polarssl_public_message(ss_polarssl_pub)(hmac, 64, hmac_cs);
  char* m = malloc(message_len + 64);
  if (m == 0) abort();
  memcpy(m, message, (unsigned int) message_len);
  memcpy(m + message_len, hmac, 64);
  /*@ polarssl_public_generated_chars_join(ss_polarssl_pub, 
                                           msg_cs, hmac_cs); @*/
  //@ chars_join(m);
  /*@ close polarssl_public_message(ss_polarssl_pub)(
                              m, message_len + 64, append(msg_cs, hmac_cs)); @*/
  net_send(&socket, m, (unsigned int) (message_len + 64));
  //@ open polarssl_public_message(ss_polarssl_pub)(m, _, _);
  
  free(m);
  //@ close [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg);
  net_close(socket);
  
  /*@ close [f2]polarssl_public_message(ss_polarssl_pub)
                                       (message, message_len, msg_cs); @*/
}

int app_receive(char *key, int key_len, char **message)
  /*@ requires [?f0]polarssl_world(ss_polarssl_pub) &*&
               [?f1]polarssl_cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
                 key_cg == polarssl_symmetric_key(?creator, ?id) &*&
               pointer(message, _);
  @*/
  /*@ ensures  [f0]polarssl_world(ss_polarssl_pub) &*&
               [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg) &*&
               pointer(message, ?message_p) &*&
                 malloc_block(message_p, result) &*&
                 polarssl_public_message(ss_polarssl_pub)
                                        (message_p, result, ?msg_cs) &*&
                 bad(creator) ? true : true == app_send_event(creator, msg_cs);
  @*/
{
  int socket1;
  int socket2;
   
  if(net_bind(&socket1, NULL, APP_RECEIVE_PORT) != 0)
    abort();
  if(net_accept(socket1, &socket2, NULL) != 0)
    abort();
  if(net_set_block(socket2) != 0)
    abort();
  
  {
    int size;
    char hmac1[64];
    char hmac2[64];
    char buffer[POLARSSL_MAX_MESSAGE_BYTE_SIZE];
    
    size = net_recv(&socket2, buffer, POLARSSL_MAX_MESSAGE_BYTE_SIZE);
    if (size <= 64 + POLARSSL_MIN_HMAC_INPUT_BYTE_SIZE) abort();
    /*@ open polarssl_public_message(ss_polarssl_pub)
                                    (buffer, size, ?cs); @*/
    size = size - 64;
    char* result = malloc(size);
    if (result == 0) abort();
    
    //@ chars_split(buffer, size);
    //@ polarssl_public_generated_chars_split(ss_polarssl_pub, cs, size);
    memcpy(result, buffer, (unsigned int) size);
    *message = result;
    //@ assert chars(result, size, ?msg_cs);
    memcpy(hmac1, (void*) buffer + size, 64);
    //@ assert chars(hmac1, 64, ?hmac_cs1);
    //@ chars_join(buffer);
    
    //@ open [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg);
    //@ close polarssl_key_id(creator, id);
    sha512_hmac(key, (unsigned int) key_len, result, 
                (unsigned int) size, hmac2, 0);
    //@ open polarssl_cryptogram(hmac2, 64, ?hmac_cs2, ?hmac_cg);
    if (memcmp(hmac1, hmac2, 64) != 0) abort();
    /*@ {
          open [_]polarssl_public_generated_chars(ss_polarssl_pub)(hmac_cs2);
          polarssl_public_generated_chars_extract(ss_polarssl_pub, hmac_cs2, hmac_cg);
          open [_]ss_polarssl_pub(hmac_cg);
          assert bad(creator) ? true : true == app_send_event(creator, msg_cs);
          close polarssl_public_message(ss_polarssl_pub)
                                       (result, size, msg_cs);
        }
    @*/
    
    //@ close [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg);
    net_close(socket1);
    net_close(socket2);
     
    return size;
  }
}

