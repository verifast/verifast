#include "enc_and_hmac.h"

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void sender(char *enc_key, char *hmac_key, char *msg, unsigned int msg_len)
/*@ requires [_]public_invar(enc_and_hmac_pub) &*&
             principal(?sender, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_cs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_cs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               shared_with(sender, enc_id) == shared_with(sender, hmac_id) &*&
             [?f3]crypto_chars(msg, msg_len, ?msg_cs) &*&
               MAX_SIZE >= msg_len &*& msg_len >= MIN_ENC_SIZE &*&
               bad(sender) || bad(shared_with(sender, enc_id)) ?
                 [_]public_generated(enc_and_hmac_pub)(msg_cs)
               :
                 true == send(sender, shared_with(sender, enc_id), msg_cs); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(enc_key, KEY_SIZE, enc_key_cs, enc_key_cg) &*&
             [f2]cryptogram(hmac_key, KEY_SIZE, hmac_key_cs, hmac_key_cg) &*&
             [f3]crypto_chars(msg, msg_len, msg_cs); @*/
{
  int socket;
  havege_state havege_state;
  
  unsigned int iv_off = 0;
  char iv[16];
  char hmac[64];
  aes_context aes_context;
  
  net_usleep(20000);
  if(net_connect(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();
  
  {
    int message_len = 16 + (int) msg_len + 64;
    char* message = malloc(message_len);
    if (message == 0) abort();
  
    // IV stuff
    //@ close havege_state(&havege_state);
    havege_init(&havege_state);
    //@ close random_request(sender, 0, false);
    if (havege_random(&havege_state, iv, 16) != 0) abort();
    //@ open cryptogram(iv, 16, ?iv_cs, ?iv_cg);
    //@ close enc_and_hmac_pub(iv_cg);
    //@ leak enc_and_hmac_pub(iv_cg);    
    //@ close optional_crypto_chars(!collision_in_run, iv, 16, iv_cs);
    memcpy(message, iv, 16);
    //@ open optional_crypto_chars(!collision_in_run, iv, 16, iv_cs);
    //@ close cryptogram(iv, 16, iv_cs, iv_cg);
    //@ close cryptogram(message, 16, iv_cs, iv_cg);
    //@ public_cryptogram(message, iv_cg);
    havege_free(&havege_state);
    //@ open havege_state(&havege_state);
    
    // encrypt
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key, 
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    //@ close [f3]optional_crypto_chars(true, msg, msg_len, msg_cs);
    {
      //@ close enc_and_hmac_proof_pred();
      //@ PRODUCE_IS_DECRYPTION_ALLOWED(enc_and_hmac)
      if (aes_crypt_cfb128(&aes_context, AES_ENCRYPT, msg_len, 
                           &iv_off, iv, msg, message + 16) != 0)
        abort();
      //@ open enc_and_hmac_proof_pred();
      //@ leak is_decryption_allowed(_, _, _);
    }
    //@ open [f3]optional_crypto_chars(true, msg, msg_len, msg_cs);
    //@ public_cryptogram(iv, iv_cg);
    //@ assert cryptogram(message + 16, msg_len, ?enc_cs, ?enc_cg);
    //@ close enc_and_hmac_pub(enc_cg);
    //@ leak enc_and_hmac_pub(enc_cg);
    //@ public_cryptogram(message + 16, enc_cg);
    //@ assert chars(message, 16 + msg_len, append(iv_cs, enc_cs));
    //@ assert enc_cg == cg_encrypted(sender, enc_id, msg_cs, iv_cs);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    
    // hmac
    //@ close [f3]optional_crypto_chars(true, msg, msg_len, msg_cs);
    sha512_hmac(hmac_key, KEY_SIZE, msg, (unsigned int) (msg_len),
                message + 16 + (int) msg_len, 0);
    //@ open [f3]optional_crypto_chars(true, msg, msg_len, msg_cs);
    //@ assert cryptogram(message + 16 + msg_len, 64, ?hmac_cs, ?hmac_cg);
    //@ assert hmac_cg == cg_hmac(sender, hmac_id, msg_cs);
    //@ close enc_and_hmac_pub(hmac_cg);
    //@ leak enc_and_hmac_pub(hmac_cg);
    //@ public_cryptogram(message + 16 + msg_len, hmac_cg);
    //@ append_assoc(iv_cs, enc_cs, hmac_cs);
    //@ chars_join(message);
    /*@ assert chars(message, message_len, 
                     append(iv_cs, append(enc_cs, hmac_cs))); @*/
    net_send(&socket, message, (unsigned int) message_len);
    
    free(message);
  }
  net_close(socket);
}

int receiver(char *enc_key, char *hmac_key, char *msg)
/*@ requires [_]public_invar(enc_and_hmac_pub) &*&
             principal(?receiver, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_cs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_cs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(?sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               receiver == shared_with(sender, enc_id) &*&
               receiver == shared_with(sender, hmac_id) &*&
             chars(msg, MAX_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(enc_key, KEY_SIZE, enc_key_cs, enc_key_cg) &*&
             [f2]cryptogram(hmac_key, KEY_SIZE, hmac_key_cs, hmac_key_cg) &*&
             chars(msg + result, MAX_SIZE - result, _) &*&
             optional_crypto_chars(!collision_in_run, msg, result, ?msg_cs) &*&
             collision_in_run || bad(sender) || bad(receiver) ||
             send(sender, receiver , msg_cs); @*/
{
  int socket1;
  int socket2;
  
  int size;
  int enc_size;
  char hmac[64];
  unsigned int temp;
  unsigned int iv_off = 0;
  char iv[16];
  aes_context aes_context;
    
  if(net_bind(&socket1, NULL, SERVER_PORT) != 0)
    abort();
  if(net_accept(socket1, &socket2, NULL) != 0)
    abort();
  if(net_set_block(socket2) != 0)
    abort();
  
  {
    int max_size = 16 + MAX_SIZE + 64;
    char *buffer = malloc (max_size); if (buffer == 0) abort();
    size = net_recv(&socket2, buffer, (unsigned int) max_size);
    if (size <= 16 + 64) abort();
    enc_size = size - 16 - 64;
    if (enc_size < MIN_ENC_SIZE) abort();
    //@ chars_split(buffer, size);
    //@ assert chars(buffer, size, ?all_cs);
    //@ close hide_chars((void*) buffer + size, max_size - size, _);
    
    // IV stuff
    //@ chars_split(buffer, 16);
    //@ assert chars(buffer, 16, ?iv_cs);
    //@ close optional_crypto_chars(false, buffer, 16, iv_cs);
    memcpy(iv, buffer, 16);
    //@ open optional_crypto_chars(false, buffer, 16, iv_cs);
    //@ open optional_crypto_chars(false, iv, 16, iv_cs);
    //@ cryptogram iv_cg = chars_for_cg_sur_random(iv_cs);
    //@ public_chars_extract(iv, iv_cg); 
    //@ if (!collision_in_run) crypto_chars(iv, 16, iv_cs);
    //@ close cryptogram(iv, 16, iv_cs, iv_cg); 
    
    //Decrypt
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key, 
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    //@ close optional_crypto_chars(false, buffer + 16, enc_size, ?enc_cs);
    {
      //@ close enc_and_hmac_proof_pred();
      //@ PRODUCE_IS_DECRYPTION_ALLOWED(enc_and_hmac)
      if (aes_crypt_cfb128(&aes_context, AES_DECRYPT, (unsigned int) enc_size,
                           &iv_off, iv, buffer + 16, msg) != 0)
        abort();
      //@ open enc_and_hmac_proof_pred();
      //@ leak is_decryption_allowed(_, _, _);
    }
    //@ open optional_crypto_chars(false, buffer + 16, enc_size, enc_cs);
    //@ public_cryptogram(iv, iv_cg);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    //@ assert optional_crypto_chars(!collision_in_run, msg, enc_size, ?dec_cs);
    //@ cryptogram enc_cg = cg_encrypted(sender, enc_id, dec_cs, iv_cs);
    //@ public_chars(buffer + 16, enc_size, enc_cs);
    //@ if (!collision_in_run) public_chars_extract(buffer + 16, enc_cg);
    //@ assert chars(buffer, 16 + enc_size, append(iv_cs, enc_cs));
    
    //Verify the hmac
    //@ assert chars(buffer + size - 64, 64, ?hmac_cs);
    //@ close optional_crypto_chars(!collision_in_run, msg, size - 80, ?pay_cs);
    sha512_hmac(hmac_key, KEY_SIZE, msg,
                (unsigned int) enc_size, hmac, 0);
    //@ open optional_crypto_chars(!collision_in_run, msg, size - 80, pay_cs);
    //@ open cryptogram(hmac, 64, ?hmac_cs2, ?hmac_cg);
    //@ close optional_crypto_chars(!collision_in_run, hmac, 64, hmac_cs2);
    //@ close optional_crypto_chars(false, (void*) buffer + size - 64, 64, _);
    if (memcmp((void*) buffer + size - 64, hmac, 64) != 0) abort();
    //@ open optional_crypto_chars(!collision_in_run, hmac, 64, hmac_cs2);
    //@ assert hmac_cg == cg_hmac(sender, hmac_id, dec_cs);
    //@ hmac_cs == hmac_cs2;
    //@ public_chars(buffer + size - 64, 64, hmac_cs);
    /*@ if (!collision_in_run) 
        {
          public_crypto_chars_extract(hmac, hmac_cg);
          public_crypto_chars(hmac, 64, hmac_cs2);
          open [_]enc_and_hmac_pub(enc_cg);
          open [_]enc_and_hmac_pub(hmac_cg);
        }
    @*/
    //@ assert all_cs == append(iv_cs, append(enc_cs, hmac_cs));
    //@ open hide_chars((void*) buffer + size, max_size - size, _);    
    //@ chars_join(buffer);
    //@ chars_join(buffer);
    free(buffer);
  }
  net_close(socket2);
  net_close(socket1);
  return enc_size;
}
