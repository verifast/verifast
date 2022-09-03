#include "auth_enc.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void sender(char *key, char *msg, unsigned int msg_len)
/*@ requires [_]public_invar(auth_enc_pub) &*&
             principal(?sender, _) &*&
             [?f1]cryptogram(key, KEY_SIZE, ?key_ccs, ?key_cg) &*&
               key_cg == cg_symmetric_key(sender, ?id) &*&
             [?f2]crypto_chars(secret, msg, msg_len, ?msg_ccs) &*&
               MAX_SIZE >= msg_len &*& msg_len >= MINIMAL_STRING_SIZE &*&
               bad(sender) || bad(shared_with(sender, id)) ?
                 [_]public_ccs(msg_ccs)
               :
                 true == send(sender, shared_with(sender, id), msg_ccs); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_ccs, key_cg) &*&
             [f2]crypto_chars(secret, msg, msg_len, msg_ccs); @*/
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
    char* message = malloc((size_t)message_len);
    if (message == 0) abort();

    // IV stuff
    //@ close havege_state(&havege_state);
    havege_init(&havege_state);
    //@ close random_request(sender, 0, false);
    if (havege_random(&havege_state, iv, 16) != 0) abort();
    //@ open cryptogram(iv, 16, ?iv_ccs, ?iv_cg);
    crypto_memcpy(message, iv, 16);
    //@ close auth_enc_pub(iv_cg);
    //@ leak auth_enc_pub(iv_cg);
    //@ close cryptogram(message, 16, iv_ccs, iv_cg);
    //@ public_cryptogram(message, iv_cg);
    //@ assert chars(message, 16, ?iv_cs);
    havege_free(&havege_state);
    //@ open havege_state(&havege_state);

    // auth encrypt
    //@ chars__split(message + 16, 16);
    //@ close gcm_context(&gcm_context);
    if (gcm_init(&gcm_context, MBEDTLS_CIPHER_ID_AES, key, 
                (unsigned int) KEY_SIZE * 8) != 0) abort();
    if (gcm_crypt_and_tag(&gcm_context, GCM_ENCRYPT, 
                          (unsigned int) msg_len,
                          iv, 16, NULL, 0, msg, message + 32, 16,
                          message + 16) != 0)
      abort();
    gcm_free(&gcm_context);
    //@ open gcm_context(&gcm_context);

    //@ assert exists(?enc_cg);
    //@ assert crypto_chars(secret, (void*) message + 16, 16, ?tag_ccs);
    //@ assert crypto_chars(secret, (void*) message + 32, msg_len, ?enc_ccs);
    //@ crypto_chars_join(message + 16);
    //@ close cryptogram(message + 16, 16 + msg_len, append(tag_ccs, enc_ccs), enc_cg);
    //@ assert enc_cg == cg_aes_auth_encrypted(sender, id, msg_ccs, iv_ccs);
    //@ close auth_enc_pub(enc_cg);
    //@ leak auth_enc_pub(enc_cg);
    //@ public_cryptogram(message + 16, enc_cg);
    //@ assert chars(message + 16, 16 + msg_len, ?tag_enc_cs);
    //@ assert append(tag_ccs, enc_ccs) == cs_to_ccs(tag_enc_cs);
    //@ chars_join(message);
    //@ assert chars(message, 16 + msg_len + 16, append(iv_cs, tag_enc_cs));
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
             [?f1]cryptogram(key, KEY_SIZE, ?key_ccs, ?key_cg) &*&
               key_cg == cg_symmetric_key(?sender, ?id) &*&
               receiver == shared_with(sender, id) &*&
             chars_(msg, MAX_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_ccs, key_cg) &*&
             chars_(msg + result, MAX_SIZE - result, _) &*&
             crypto_chars(secret, msg, result, ?msg_ccs) &*&
             col || bad(sender) || bad(receiver) ||
               send(sender, receiver, msg_ccs); @*/
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
    char *buffer = malloc ((size_t)max_size); if (buffer == 0) abort();
    size = net_recv(&socket2, buffer, (unsigned int) max_size);
    if (size <= 16 + 16) abort();
    enc_size = size - 16 - 16;
    if (enc_size < MINIMAL_STRING_SIZE) abort();
    //@ chars_split(buffer, 16);
    //@ chars_split(buffer + 16, 16);
    //@ assert chars(buffer, 16, ?iv_cs);
    //@ interpret_nonce(buffer, 16);
    //@ open cryptogram(buffer, 16, ?iv_ccs, _);
    //@ assert chars(buffer + 16, 16, ?tag_cs);
    //@ assert chars(buffer + 32, enc_size, ?enc_cs);
    
    // auth decrypt
    //@ close gcm_context(&gcm_context);
    if (gcm_init(&gcm_context, MBEDTLS_CIPHER_ID_AES, key, 
                (unsigned int) KEY_SIZE * 8) != 0) abort();
    //@ interpret_auth_encrypted(buffer + 16, 16 + enc_size);
    //@ open cryptogram(buffer + 16, 16 + enc_size, ?enc_ccs, ?enc_cg);
    //@ close exists(enc_cg);
    //@ crypto_chars_split(buffer + 16, 16);
    if (gcm_auth_decrypt(&gcm_context, (unsigned int) enc_size,
                         buffer, 16, NULL, 0, buffer + 16, 16,
                         buffer + 32, msg) != 0)
      abort();
    //@ crypto_chars_join(buffer + 16);
    //@ public_crypto_chars(buffer + 16, 16 + enc_size);
    gcm_free(&gcm_context);
    //@ open gcm_context(&gcm_context);
    /*@ if (!col)
        {
          assert enc_cg == cg_aes_auth_encrypted(sender, id, ?dec_ccs, iv_ccs);
          assert ccs_for_cg(enc_cg) == enc_ccs;
          enc_ccs == cs_to_ccs(append(tag_cs, enc_cs));
          open [_]auth_enc_pub(enc_cg);
        }
    @*/
    zeroize(buffer, 16);
    //@ chars_join(buffer);
    free(buffer);
  }
  net_close(socket2);
  net_close(socket1);
  return enc_size;
  //@ close principal(receiver, _);
}
