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
                 cg_info(enc_key_cg) == hmac_id &*&
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

  unsigned int iv_off = 0;
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

    int message_len = 16 + enc_len;
    char* message = malloc(message_len);
    if (message == 0) abort();

    // IV stuff
    //@ close havege_state(&havege_state);
    havege_init(&havege_state);
    //@ close random_request(sender, 0, false);
    if (havege_random(&havege_state, iv, 16) != 0) abort();
    //@ open cryptogram(iv, 16, ?iv_cs, ?iv_cg);
    //@ close hmac_then_enc_pub(iv_cg);
    //@ leak hmac_then_enc_pub(iv_cg);    
    //@ close optional_crypto_chars(!collision_in_run, iv, 16, iv_cs);
    memcpy(message, iv, 16);
    //@ open optional_crypto_chars(!collision_in_run, iv, 16, iv_cs);
    //@ close cryptogram(iv, 16, iv_cs, iv_cg);
    //@ close cryptogram(message, 16, iv_cs, iv_cg);
    //@ public_cryptogram(message, iv_cg);
    havege_free(&havege_state);
    //@ open havege_state(&havege_state);
    //@ assert chars(message, 16, iv_cs);

    // encrypt
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key,
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    //@ close cryptogram(iv, 16, iv_cs, iv_cg);
    //@ close optional_crypto_chars(true, enc_msg, msg_len + 64, enc_msg_cs);    
    {
      //@ close hmac_then_enc_proof_pred();
      //@ PRODUCE_IS_DECRYPTION_ALLOWED(hmac_then_enc)
      if (aes_crypt_cfb128(&aes_context, AES_ENCRYPT, msg_len + 64,
                           &iv_off, iv, enc_msg, message + 16) != 0)
        abort();
      //@ open hmac_then_enc_proof_pred();
      //@ leak is_decryption_allowed(_, _, _);
    }
    //@ open optional_crypto_chars(true, enc_msg, msg_len + 64, enc_msg_cs);
    //@ public_cryptogram(iv, iv_cg);
    //@ assert cryptogram(message + 16, msg_len + 64, ?enc_cs, ?enc_cg);
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
    /*@ if (collision_in_run || hmac_then_enc_public_key(sender, enc_id))
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
    //@ public_cryptogram(message + 16, enc_cg);
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
                 cg_info(enc_key_cg) == hmac_id &*&
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

  int size;
  int enc_size;
  char hmac[64];
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
    int max_size = 20 + MAX_SIZE + 64;
    char *buffer = malloc (max_size); if (buffer == 0) abort();
    size = net_recv(&socket2, buffer, (unsigned int) max_size);
    if (size <= 16 + 64) abort();
    enc_size = size - 16;
    if (enc_size < MIN_ENC_SIZE || enc_size > MAX_SIZE) abort();
    if (enc_size -64 < MIN_HMAC_INPUT_SIZE) abort();
    char *buffer_dec = malloc (enc_size); if (buffer_dec == 0) abort();

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
      //@ close hmac_then_enc_proof_pred();
      //@ PRODUCE_IS_DECRYPTION_ALLOWED(hmac_then_enc)
      if (aes_crypt_cfb128(&aes_context, AES_DECRYPT, (unsigned int) enc_size,
                           &iv_off, iv, buffer + 16, buffer_dec) != 0)
        abort();
      //@ open hmac_then_enc_proof_pred();
      //@ leak is_decryption_allowed(_, _, _);
    }
    
    //@ open optional_crypto_chars(false, buffer + 16, enc_size, enc_cs);
    //@ public_cryptogram(iv, iv_cg);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    /*@ open optional_crypto_chars(!collision_in_run,
                                   buffer_dec, enc_size, ?dec_cs); @*/
    //@ cryptogram enc_cg = cg_encrypted(sender, enc_id, dec_cs, iv_cs);
    //@ if (!collision_in_run) public_chars_extract(buffer + 16, enc_cg);

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
    //@ chars_split(msg, enc_size);
    memcpy(msg, buffer_dec, (unsigned int) enc_size - 64);
    /*@ open optional_crypto_chars(!collision_in_run,
                                   buffer_dec, enc_size - 64, pay_cs); @*/
    /*@ if (!collision_in_run && !hmac_then_enc_public_key(sender, enc_id))
        {
          open [_]hmac_then_enc_pub(enc_cg);
          assert [_]hmac_then_enc_pub_1(?msg_cs, ?hmac_cg2);
          assert length(pay_cs) == length(msg_cs);
          drop_append(length(pay_cs), msg_cs, chars_for_cg(hmac_cg2));
          drop_append(length(pay_cs), pay_cs, chars_for_cg(hmac_cg));
          assert (chars_for_cg(hmac_cg) == chars_for_cg(hmac_cg2));
          chars_for_cg_inj_hmac(hmac_cg, hmac_cg2);
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
