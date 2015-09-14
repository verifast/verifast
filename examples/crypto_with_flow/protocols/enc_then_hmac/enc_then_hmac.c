#include "enc_then_hmac.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void sender(char *enc_key, char *hmac_key, char *msg, unsigned int msg_len)
/*@ requires [_]public_invar(enc_then_hmac_pub) &*&
             principal(?sender, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_cs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_cs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               shared_with(sender, enc_id) == shared_with(sender, hmac_id) &*&
             [?f3]crypto_chars(msg, msg_len, ?msg_cs) &*&
               MAX_SIZE >= msg_len &*& msg_len >= MIN_ENC_SIZE &*&
               bad(sender) || bad(shared_with(sender, enc_id)) ?
                 [_]public_generated(enc_then_hmac_pub)(msg_cs)
               :
                 true == send(sender, shared_with(sender, enc_id), msg_cs); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(enc_key, KEY_SIZE, enc_key_cs, enc_key_cg) &*&
             [f2]cryptogram(hmac_key, KEY_SIZE, hmac_key_cs, hmac_key_cg) &*&
             [f3]crypto_chars(msg, msg_len, msg_cs); @*/
{
  int socket;
  havege_state havege_state;
  
  unsigned int temp;
  int iv_off;
  char iv[16];
  char hmac[64];
  
  net_usleep(20000);
  if(net_connect(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();
  
  {
    aes_context aes_context;
    int message_len = 4 + 16 + (int) msg_len + 64;
    char* message = malloc(message_len);
    if (message == 0) abort();
  
    // IV stuff
    //@ close havege_state(&havege_state);
    havege_init(&havege_state);
    /*@ DEFAULT_HAVEGE_UTIL_INIT(enc_then_hmac_pub, 
                                 enc_then_hmac_proof_pred, sender) @*/
    r_int_with_bounds(&havege_state, &iv_off, 0, 15);
    //@ close random_request(sender, 0, false);
    if (havege_random(&havege_state, iv, 16) != 0) abort();  
    //@ assert integer(&iv_off, ?iv_val) &*& iv_val >=0 &*& iv_val <= 15;
    //@ assert cryptogram(iv, 16, ?iv_cs, ?iv_cg);
    //@ close enc_then_hmac_pub(iv_cg);
    //@ leak enc_then_hmac_pub(iv_cg);
    //@ public_cryptogram(iv, iv_cg);
    //@ integer_to_chars(&iv_off);
    /*@ close optional_crypto_chars(false, (void*) &iv_off, 
                                    4, chars_of_int(iv_val)); @*/
    memcpy(message, &iv_off, 4);
    /*@ open optional_crypto_chars(false, (void*) &iv_off, 
                                   4, chars_of_int(iv_val)); @*/
    //@ open optional_crypto_chars(false, message, 4, chars_of_int(iv_val));
    //@ chars_to_integer(&iv_off);
    //@ close optional_crypto_chars(false, iv, 16, iv_cs);
    memcpy(message + 4, iv, 16);
    //@ open optional_crypto_chars(false, iv, 16, iv_cs);
    //@ open optional_crypto_chars(false, message + 4, 16, iv_cs);
    //@ chars_join(message);
    //@ list<char> ent = append(chars_of_int(iv_val), iv_cs);
    //@ assert chars(message, 20, ent);
    //@ assert chars(message + 20, msg_len + 64, _);
    havege_free(&havege_state);
    /*@ DEFAULT_HAVEGE_UTIL_EXIT(enc_then_hmac_pub, 
                                 enc_then_hmac_proof_pred, sender) @*/
    //@ open havege_state(&havege_state);
    
    // encrypt
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key, 
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    //@ close [f3]optional_crypto_chars(true, msg, msg_len, msg_cs);
    temp = (unsigned int) iv_off;
    if (aes_crypt_cfb128(&aes_context, AES_ENCRYPT, msg_len, 
                         &temp, iv, msg, message + 20) != 0)
      abort();
    //@ open [f3]optional_crypto_chars(true, msg, msg_len, msg_cs);
    //@ assert cryptogram(message + 20, msg_len, ?enc_cs, ?enc_cg);
    //@ close enc_then_hmac_pub(enc_cg);
    //@ leak enc_then_hmac_pub(enc_cg);
    //@ public_cryptogram(message + 20, enc_cg);
    //@ append_assoc(chars_of_int(iv_val), iv_cs, enc_cs);
    //@ assert chars(message, 20 + msg_len, append(ent, enc_cs));
    //@ assert enc_cg == cg_encrypted(sender, enc_id, msg_cs, ent);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    
    // hmac
    /*@ close optional_crypto_chars(false, message, 20 + msg_len, 
                                    append(ent, enc_cs)); @*/
    sha512_hmac(hmac_key, KEY_SIZE, message, 
                (unsigned int) (20 + (int) msg_len), 
                message + 20 + (int) msg_len, 0);
    /*@ open optional_crypto_chars(false, message, 20 + msg_len, 
                                   append(ent, enc_cs)); @*/       
    //@ assert cryptogram(message + 20 + msg_len, 64, ?hmac_cs, ?hmac_cg);
    //@ assert hmac_cg == cg_hmac(sender, hmac_id, append(ent, enc_cs));
    /*@ if (!bad(sender) && !bad(shared_with(sender, enc_id))) 
          close enc_then_hmac_pub_1(enc_id, msg_cs, ent); @*/
    //@ close enc_then_hmac_pub(hmac_cg);
    //@ leak enc_then_hmac_pub(hmac_cg);
    //@ public_cryptogram(message + 20 + msg_len, hmac_cg);
    //@ append_assoc(ent, enc_cs, hmac_cs);
    /*@ assert chars(message, message_len, 
                     append(ent, append(enc_cs, hmac_cs))); @*/
    net_send(&socket, message, (unsigned int) message_len);
    
    free(message);
  }
  net_close(socket);
}

int receiver(char *enc_key, char *hmac_key, char *msg)
/*@ requires [_]public_invar(enc_then_hmac_pub) &*&
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
             crypto_chars(msg, result, ?msg_cs) &*&
             bad(sender) || bad(receiver) || collision_in_run() ||
             send(sender, receiver, msg_cs); @*/
{
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
    int max_size = 20 + MAX_SIZE + 64;
    char hmac[64];
    unsigned int temp;
    int iv_off;
    char iv[16];
    aes_context aes_context;
    char *buffer = malloc (max_size); if (buffer == 0) abort();
    size = net_recv(&socket2, buffer, (unsigned int) max_size);
    if (size <= 20 + 64) abort();
    enc_size = size - 20 - 64;
    if (enc_size < MIN_ENC_SIZE) abort();
    //@ chars_split(buffer, size);
    //@ assert chars(buffer, size, ?all_cs);
    //@ close hide_chars((void*) buffer + size, max_size - size, _);

    //Verify the hmac
    //@ chars_split(buffer, size - 64);
    //@ assert chars(buffer + size - 64, 64, ?hmac_cs);
    //@ close optional_crypto_chars(false, buffer, size - 64, ?pay_cs);
    sha512_hmac(hmac_key, KEY_SIZE, buffer, 
                (unsigned int) (size - 64), hmac, 0);
    //@ open optional_crypto_chars(false, buffer, size - 64, pay_cs);
    //@ open cryptogram(hmac, 64, ?hmac_cs2, ?hmac_cg);
    //@ close optional_crypto_chars(true, hmac, 64, hmac_cs2);
    //@ close optional_crypto_chars(false, (void*) buffer + size - 64, 64, _);
    if (memcmp((void*) buffer + size - 64, hmac, 64) != 0) abort();
    //@ open optional_crypto_chars(true, hmac, 64, hmac_cs2);
    //@ open optional_crypto_chars(false, (void*) buffer + size - 64, 64, _);
    //@ hmac_cs == hmac_cs2;
    //@ public_chars(buffer + size - 64, 64, hmac_cs);
    //@ public_crypto_chars_extract(hmac, hmac_cg);
    //@ public_crypto_chars(hmac, 64, hmac_cs2);
    //@ assert all_cs == append(pay_cs, hmac_cs);
    
    // IV stuff
    //@ chars_split(buffer, 20);
    //@ assert chars(buffer, 20, ?prefix);
    //@ chars_split(buffer, 4);
    //@ assert chars(buffer, 4, ?iv_off_cs);
    //@ assert chars(buffer + 4, 16, ?iv_cs);
    //@ chars_to_integer(buffer);
    iv_off = *((int*) (void*) buffer);
    if (iv_off < 0 || iv_off >= 16) abort();
    //@ integer_to_chars(buffer);
    //@ close optional_crypto_chars(false, buffer + 4, 16, iv_cs);
    memcpy(iv, buffer + 4, 16);
    //@ open optional_crypto_chars(false, buffer + 4, 16, iv_cs);
    //@ assert iv_off_cs == chars_of_int(iv_off);
    //@ assert prefix == append(iv_off_cs, iv_cs);
    //@ chars_join(buffer);
    
    //Decrypt
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key, 
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    //@ close optional_crypto_chars(false, buffer + 20, enc_size, ?enc_cs);
    temp = (unsigned int) iv_off;
    if (aes_crypt_cfb128(&aes_context, AES_DECRYPT, (unsigned int) enc_size,
                         &temp, iv, buffer + 20, msg) != 0)
      abort();
    //@ open optional_crypto_chars(false, buffer + 20, enc_size, enc_cs);
    //@ assert pay_cs == append(prefix, enc_cs);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    //@ assert crypto_chars(msg, enc_size, ?dec_cs);
    //@ cryptogram enc_cg = cg_encrypted(sender, enc_id, dec_cs, prefix);
    //@ public_chars(buffer + 20, enc_size, enc_cs);
    //@ public_chars_extract(buffer + 20, enc_cg);
    //@ open [_]enc_then_hmac_pub(enc_cg);
    //@ open [_]enc_then_hmac_pub(hmac_cg);
    /*@ if (!bad(sender) && !bad(shared_with(sender, enc_id)) && 
            !collision_in_run())
        {
          assert [_]enc_then_hmac_pub_1(?id, ?dec_cs2, ?ent);
          cryptogram enc_cg2 = cg_encrypted(sender, id, dec_cs2, ent);
          assert pay_cs == append(prefix, chars_for_cg(enc_cg));
          assert pay_cs == append(ent, chars_for_cg(enc_cg2));
          take_append(20, prefix, chars_for_cg(enc_cg));
          take_append(20, ent, chars_for_cg(enc_cg2));
          assert ent == prefix;
          drop_append(20, prefix, chars_for_cg(enc_cg));
          drop_append(20, ent, chars_for_cg(enc_cg2));
          assert chars_for_cg(enc_cg) == chars_for_cg(enc_cg2);
          chars_for_cg_inj(enc_cg, enc_cg2);
          assert dec_cs == dec_cs2;
        }
    @*/
    //@ open hide_chars((void*) buffer + size, max_size - size, _);    
    //@ chars_join(buffer);
    //@ chars_join(buffer);
    free(buffer);
  }
  net_close(socket2);
  net_close(socket1);
  return enc_size;
}
