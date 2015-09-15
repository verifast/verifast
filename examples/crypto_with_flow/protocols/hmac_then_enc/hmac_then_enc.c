#include "hmac_then_enc.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void sender(char *enc_key, char *hmac_key, char *msg, unsigned int msg_len)
/*@ requires [_]public_invar(hmac_then_enc_pub) &*&
             principal(?sender, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_cs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_cs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               shared_with(sender, enc_id) == shared_with(sender, hmac_id) &*&
             [?f3]crypto_chars(msg, msg_len, ?msg_cs) &*&
               MAX_SIZE >= msg_len &*& msg_len >= MIN_ENC_SIZE &*&
               collision_in_run || bad(sender) || 
               bad(shared_with(sender, enc_id)) ?
                 [_]public_generated(hmac_then_enc_pub)(msg_cs)
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
    int enc_len = (int) msg_len + 64;
    char* enc_msg = malloc(enc_len);
    if (enc_msg == 0) abort();
  
    // Copy message
    //@ chars_split(enc_msg, msg_len);
    //@ close [f3]optional_crypto_chars(true, msg, msg_len, msg_cs);
    memcpy(enc_msg, msg, msg_len);
    //@ assert crypto_chars(enc_msg, msg_len, msg_cs);

    // hmac
    sha512_hmac(hmac_key, KEY_SIZE, msg, msg_len, 
                enc_msg + (int) msg_len, 0);
    //@ open [f3]optional_crypto_chars(true, msg, msg_len, msg_cs);       
    //@ open cryptogram(enc_msg + msg_len, 64, ?hmac_cs, ?hmac_cg);
    /*@ if (collision_in_run) 
        {
          public_chars(enc_msg + msg_len, 64, hmac_cs);
          crypto_chars(enc_msg + msg_len, 64, hmac_cs);
        }
    @*/
    //@ open optional_crypto_chars(true, enc_msg, msg_len, msg_cs);
    //@ crypto_chars_join(enc_msg);
    //@ list<char> enc_msg_cs = append(msg_cs, hmac_cs);
    //@ assert crypto_chars(enc_msg, msg_len + 64, enc_msg_cs);
    
    int message_len = 4 + 16 + enc_len;
    char* message = malloc(message_len);
    if (message == 0) abort();
    
    // IV stuff
    //@ close havege_state(&havege_state);
    havege_init(&havege_state);
    /*@ DEFAULT_HAVEGE_UTIL_INIT(hmac_then_enc_pub, 
                                 hmac_then_enc_proof_pred, sender) @*/
    r_int_with_bounds(&havege_state, &iv_off, 0, 15);
    //@ close random_request(sender, 0, false);
    if (havege_random(&havege_state, iv, 16) != 0) abort();  
    //@ assert integer(&iv_off, ?iv_val) &*& iv_val >=0 &*& iv_val <= 15;
    //@ assert cryptogram(iv, 16, ?iv_cs, ?iv_cg);
    //@ close hmac_then_enc_pub(iv_cg);
    //@ leak hmac_then_enc_pub(iv_cg);
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
    havege_free(&havege_state);
    /*@ DEFAULT_HAVEGE_UTIL_EXIT(hmac_then_enc_pub, 
                                 hmac_then_enc_proof_pred, sender) @*/
    //@ open havege_state(&havege_state);
    //@ assert chars(message, 20, ent);
    //@ assert chars(message + 20, msg_len + 64, _);
    
    // encrypt
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key, 
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    //@ close optional_crypto_chars(true, enc_msg, msg_len + 64, enc_msg_cs);
    temp = (unsigned int) iv_off;
    if (aes_crypt_cfb128(&aes_context, AES_ENCRYPT, msg_len + 64, 
                         &temp, iv, enc_msg, message + 20) != 0)
      abort();
    //@ open optional_crypto_chars(true, enc_msg, msg_len + 64, enc_msg_cs);
    //@ assert cryptogram(message + 20, msg_len + 64, ?enc_cs, ?enc_cg);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    
    //@ close hmac_then_enc_pub(hmac_cg);
    //@ leak hmac_then_enc_pub(hmac_cg);
    //@ take_append(msg_len, msg_cs, hmac_cs);    
    //@ drop_append(msg_len, msg_cs, hmac_cs);
    //@ crypto_chars_split(enc_msg, msg_len);
    /*@ if (collision_in_run) 
          public_crypto_chars(enc_msg + msg_len, 64, hmac_cs); @*/
    //@ close cryptogram(enc_msg + msg_len, 64, hmac_cs, hmac_cg);
    //@ public_cryptogram(enc_msg + msg_len, hmac_cg);
    //@ public_chars(enc_msg + msg_len, 64, hmac_cs);
    /*@ if (collision_in_run || bad(sender) || bad(shared_with(sender, enc_id)))
        {
          assert [_]public_generated(hmac_then_enc_pub)(msg_cs);
          assert [_]public_generated(hmac_then_enc_pub)(hmac_cs);
          public_crypto_chars(enc_msg, msg_len, msg_cs);
          assert chars(enc_msg, msg_len, msg_cs);
          assert chars(enc_msg + msg_len, 64, hmac_cs);
          chars_join(enc_msg);
          public_chars(enc_msg, msg_len + 64, append(msg_cs, hmac_cs));
          chars_split(enc_msg, msg_len);
          crypto_chars(enc_msg, msg_len, msg_cs);
        }
        else
        {
          close hmac_then_enc_pub_1(msg_cs, hmac_cg);
        }
    @*/
    //@ close hmac_then_enc_pub(enc_cg);
    //@ leak hmac_then_enc_pub(enc_cg);
    //@ public_cryptogram(message + 20, enc_cg);
    net_send(&socket, message, (unsigned int) message_len);
    //@ crypto_chars(enc_msg + msg_len, 64, hmac_cs);
    //@ crypto_chars_join(enc_msg);
    //@ close optional_crypto_chars(true, enc_msg, msg_len + 64, enc_msg_cs);
    zeroize(enc_msg, enc_len);
    free(enc_msg);
    free(message);
  }
  net_close(socket);
}

int receiver(char *enc_key, char *hmac_key, char *msg)
/*@ requires [_]public_invar(hmac_then_enc_pub) &*&
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
    enc_size = size - 20;
    if (enc_size < MIN_ENC_SIZE || enc_size > MAX_SIZE) abort();
    if (enc_size -64 < MIN_HMAC_INPUT_SIZE) abort();
    char *buffer_dec = malloc (enc_size); if (buffer_dec == 0) abort();
    
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
                         &temp, iv, buffer + 20, buffer_dec) != 0)
      abort();
    //@ open optional_crypto_chars(false, buffer + 20, enc_size, enc_cs);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    /*@ open optional_crypto_chars(!collision_in_run,
                                   buffer_dec, enc_size, ?dec_cs); @*/
    //@ cryptogram enc_cg = cg_encrypted(sender, enc_id, dec_cs, prefix);
    //@ if (!collision_in_run) public_chars_extract(buffer + 20, enc_cg);
    
    //Verify the hmac
    //@ if (!collision_in_run) crypto_chars_split(buffer_dec, enc_size - 64);
    /*@ close optional_crypto_chars(!collision_in_run,
                                    buffer_dec, enc_size - 64, ?pay_cs); @*/
    sha512_hmac(hmac_key, KEY_SIZE, buffer_dec, 
                (unsigned int) (enc_size - 64), hmac, 0);
    //@ assert cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
    //@ close hmac_then_enc_pub(hmac_cg);
    //@ leak hmac_then_enc_pub(hmac_cg);
    //@ public_cryptogram(hmac, hmac_cg);
    /*@ close optional_crypto_chars(!collision_in_run, 
                                 buffer_dec + enc_size - 64, 64, ?hmac_cs2); @*/
    //@ close optional_crypto_chars(false, hmac, 64, _);
    if (memcmp(hmac, (void*) buffer_dec + enc_size - 64, 64) != 0) abort();
    /*@ open optional_crypto_chars(!collision_in_run, 
                                  buffer_dec + enc_size - 64, 64, hmac_cs2); @*/
    //@ open optional_crypto_chars(false, hmac, 64, hmac_cs2);
    //@ cryptogram hmac_cg2 = chars_for_cg_sur(hmac_cs2, CG_HMAC_TAG);
    //@ chars_split(msg, enc_size);
    memcpy(msg, buffer_dec, (unsigned int) enc_size - 64);
    /*@ open optional_crypto_chars(!collision_in_run, 
                                   buffer_dec, enc_size - 64, pay_cs); @*/
    /*@ if (!collision_in_run && !bad(sender) && 
            !bad(shared_with(sender, enc_id)))
        {
          open [_]hmac_then_enc_pub(enc_cg);
          assert [_]hmac_then_enc_pub_1(?msg_cs, ?hmac_cg3);
          assert length(pay_cs) == length(msg_cs);
          drop_append(length(pay_cs), msg_cs, chars_for_cg(hmac_cg3));
          drop_append(length(pay_cs), pay_cs, chars_for_cg(hmac_cg));
          assert (chars_for_cg(hmac_cg) == chars_for_cg(hmac_cg3));
          chars_for_cg_inj(hmac_cg, hmac_cg3);
          assert pay_cs == msg_cs;
        }
    @*/
    //@ chars_join(buffer);
    free(buffer);
    //@ if (!collision_in_run) crypto_chars_join(buffer_dec);
    //@ close optional_crypto_chars(!collision_in_run, buffer_dec, enc_size, _);
    zeroize(buffer_dec, enc_size);
    free(buffer_dec);
  }
  net_close(socket2);
  net_close(socket1);
  return enc_size - 64;
}
