#include "auth_enc.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void sender(char *key, char *msg, unsigned int msg_len)
/*@ requires [_]public_invar(auth_enc_pub) &*&
             principal(?sender, _) &*&
             [?f1]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
               key_cg == cg_symmetric_key(sender, ?id) &*&
             [?f2]crypto_chars(secret, msg, msg_len, ?msg_cs) &*&
               MAX_SIZE >= msg_len &*& msg_len >= MINIMAL_STRING_SIZE &*&
               bad(sender) || bad(shared_with(sender, id)) ?
                 [_]public_generated(auth_enc_pub)(msg_cs)
               :
                 true == send(sender, shared_with(sender, id), msg_cs); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_cs, key_cg) &*&
             [f2]crypto_chars(secret, msg, msg_len, msg_cs); @*/
{
  //@ open principal(sender, _);
  int socket;
  havege_state havege_state;
  
  unsigned int temp;
  char iv[16];
  
  net_usleep(20000);
  if(net_connect(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();
  
  {
    gcm_context gcm_context;
    int message_len = 16 + (int) msg_len + 16;
    char* message = malloc(message_len);
    if (message == 0) abort();

    // IV stuff
    //@ close havege_state(&havege_state);
    havege_init(&havege_state);
    //@ close random_request(sender, 0, false);
    if (havege_random(&havege_state, iv, 16) != 0) abort();
    //@ open cryptogram(iv, 16, ?iv_cs, ?iv_cg);
    memcpy(message, iv, 16);
    //@ close auth_enc_pub(iv_cg);
    //@ leak auth_enc_pub(iv_cg);
    //@ close cryptogram(message, 16, iv_cs, iv_cg);
    //@ public_cryptogram(message, iv_cg);
    havege_free(&havege_state);
    //@ open havege_state(&havege_state);

    // auth encrypt
    //@ chars_split(message + 16, msg_len);
    //@ close gcm_context(&gcm_context);
    if (gcm_init(&gcm_context, POLARSSL_CIPHER_ID_AES, key, 
                (unsigned int) KEY_SIZE * 8) != 0) abort();
    if (gcm_crypt_and_tag(&gcm_context, GCM_ENCRYPT, 
                          (unsigned int) msg_len,
                          iv, 16, NULL, 0, msg, message + 16, 16,
                          message + 16 + (int) msg_len) != 0)
      abort();
    gcm_free(&gcm_context);
    //@ open gcm_context(&gcm_context);

    //@ assert cryptogram(message + 16, msg_len, ?enc_cs, ?enc_cg);
    //@ assert chars(message + 16 + msg_len, 16, ?tag_cs);
    //@ assert enc_cg == cg_auth_encrypted(sender, id, msg_cs, tag_cs, iv_cs);
    //@ close auth_enc_pub(enc_cg);
    //@ leak auth_enc_pub(enc_cg);
    //@ public_cryptogram(message + 16, enc_cg);
    //@ chars_join(message + 16);
    //@ assert chars(message + 16, msg_len + 16, append(enc_cs, tag_cs));
    //@ chars_join(message);
    /*@ assert chars(message, 16 + msg_len + 16, 
                     append(iv_cs, append(enc_cs, tag_cs))); @*/
    net_send(&socket, message, (unsigned int) message_len);
    zeroize(iv, 16);
    free(message);
  }
  net_close(socket);
  //@ close principal(sender, _);
}

int receiver(char *key, char *msg)
/*@ requires [_]public_invar(auth_enc_pub) &*&
             principal(?receiver, _) &*&
             [?f1]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
               key_cg == cg_symmetric_key(?sender, ?id) &*&
               receiver == shared_with(sender, id) &*&
             chars(msg, MAX_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_cs, key_cg) &*&
             chars(msg + result, MAX_SIZE - result, _) &*&
             crypto_chars(secret, msg, result, ?msg_cs) &*&
             col || bad(sender) || bad(receiver) ||
               send(sender, receiver, msg_cs); @*/
{
  //@ open principal(receiver, _);
  int socket1;
  int socket2;
  
  if(net_bind(&socket1, NULL, SERVER_PORT) != 0)
    abort();
  if(net_accept(socket1, &socket2, NULL) != 0)
    abort();
  if(net_set_block(socket2) != 0)
    abort();
  
  int size;
  int enc_size;
  {
    int max_size = 16 + MAX_SIZE + 16;
    gcm_context gcm_context;
    char *buffer = malloc (max_size); if (buffer == 0) abort();
    size = net_recv(&socket2, buffer, (unsigned int) max_size);
    if (size <= 16 + 16) abort();
    enc_size = size - 16 - 16;
    if (enc_size < MINIMAL_STRING_SIZE) abort();
    //@ chars_split(buffer, size);
    //@ assert chars(buffer, size, ?all_cs);
    //@ close hide_chars((void*) buffer + size, max_size - size, _);
    //@ chars_split(buffer, 16);
    //@ chars_split(buffer + 16, enc_size);
    //@ assert chars(buffer, 16, ?iv_cs);
    //@ interpret_nonce(buffer, 16);
    //@ open cryptogram(buffer, 16, iv_cs, _);
    //@ assert chars(buffer + 16, enc_size, ?enc_cs);
    //@ assert chars(buffer + 16 + enc_size, 16, ?tag_cs);
    
    // auth decrypt
    //@ close gcm_context(&gcm_context);
    if (gcm_init(&gcm_context, POLARSSL_CIPHER_ID_AES, key, 
                (unsigned int) KEY_SIZE * 8) != 0) abort();
    //@ interpret_auth_encrypted(buffer + 16, enc_size);
    //@ open cryptogram(buffer + 16, enc_size, enc_cs, ?enc_cg);
    //@ close cryptogram(buffer + 16, enc_size, enc_cs, enc_cg);
    if (gcm_auth_decrypt(&gcm_context, (unsigned int) enc_size,
                         buffer, 16, NULL, 0, buffer + 16 + enc_size, 16,
                         buffer + 16, msg) != 0)
      abort();
    //@ public_cryptogram(buffer + 16, enc_cg);
    gcm_free(&gcm_context);
    //@ open gcm_context(&gcm_context);
    
    /*@ if (!col)
        {
          assert enc_cg == cg_auth_encrypted(sender, id, ?dec_cs, tag_cs, iv_cs);
          assert chars_for_cg(enc_cg) == enc_cs;
          public_chars_extract(buffer + 16, enc_cg);
          open [_]auth_enc_pub(enc_cg);
        }
    @*/
    //@ open hide_chars((void*) buffer + size, max_size - size, _);
    //@ chars_join(buffer + 16);
    zeroize(buffer, 16);
    //@ chars_join(buffer);
    //@ chars_join(buffer);
    free(buffer);
  }
  net_close(socket2);
  net_close(socket1);
  return enc_size;
  //@ close principal(receiver, _);
}
