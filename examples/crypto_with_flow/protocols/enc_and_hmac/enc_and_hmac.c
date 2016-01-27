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
             [?f3]crypto_chars(secret, msg, msg_len, ?msg_cs) &*&
               MAX_SIZE >= msg_len &*& msg_len >= MINIMAL_STRING_SIZE &*&
               bad(sender) || bad(shared_with(sender, enc_id)) ?
                 [_]public_generated(enc_and_hmac_pub)(msg_cs)
               :
                 true == send(sender, shared_with(sender, enc_id), msg_cs); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(enc_key, KEY_SIZE, enc_key_cs, enc_key_cg) &*&
             [f2]cryptogram(hmac_key, KEY_SIZE, hmac_key_cs, hmac_key_cg) &*&
             [f3]crypto_chars(secret, msg, msg_len, msg_cs); @*/
{
  //@ open principal(sender, _);
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
    memcpy(message, iv, 16);
    //@ close cryptogram(message, 16, iv_cs, iv_cg);
    //@ public_cryptogram(message, iv_cg);
    havege_free(&havege_state);
    //@ open havege_state(&havege_state);

    // encrypt
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key,
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    if (aes_crypt_cfb128(&aes_context, AES_ENCRYPT, msg_len,
                         &iv_off, iv, msg, message + 16) != 0)
      abort();
    //@ assert cryptogram(message + 16, msg_len, ?enc_cs, ?enc_cg);
    //@ close enc_and_hmac_pub(enc_cg);
    //@ leak enc_and_hmac_pub(enc_cg);
    //@ public_cryptogram(message + 16, enc_cg);
    //@ assert chars(message, 16 + msg_len, append(iv_cs, enc_cs));
    //@ assert enc_cg == cg_encrypted(sender, enc_id, msg_cs, iv_cs);
    zeroize(iv, 16);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);

    // hmac
    sha512_hmac(hmac_key, KEY_SIZE, msg, (unsigned int) (msg_len),
                message + 16 + (int) msg_len, 0);
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
  //@ close principal(sender, _);
}

int receiver(char *enc_key, char *hmac_key, char *msg)
/*@ requires [_]public_invar(enc_and_hmac_pub) &*&
             [_]decryption_key_classifier(enc_and_hmac_public_key) &*&
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
             crypto_chars(secret, msg, result, ?msg_cs) &*&
             col || bad(sender) || bad(receiver) ||
               send(sender, receiver , msg_cs); @*/
{
  //@ open principal(receiver, _);
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
    if (enc_size < MINIMAL_STRING_SIZE) abort();
    //@ chars_split(buffer, size);
    //@ assert chars(buffer, size, ?all_cs);
    //@ close hide_chars((void*) buffer + size, max_size - size, _);

    // Interpret message
    //@ chars_split(buffer, 16);
    //@ assert chars(buffer, 16, ?iv_cs);
    //@ chars_to_crypto_chars(buffer, 16);
    memcpy(iv, buffer, 16);
    //@ interpret_nonce(iv, 16);
    //@ open cryptogram(iv, 16, iv_cs, ?iv_cg);

    //@ assert chars(buffer + 16, enc_size, ?enc_cs);
    //@ interpret_encrypted(buffer + 16, enc_size);
    //@ open cryptogram(buffer + 16, enc_size, enc_cs, ?enc_cg);
    //@ close cryptogram(buffer + 16, enc_size, enc_cs, enc_cg);
    //@ assert enc_cg == cg_encrypted(?p2, ?c2, ?dec_cs2, ?iv_cs2);
    
    //@ assert chars(buffer + 16 + enc_size, 64, ?hmac_cs);
    //@ interpret_hmac(buffer + 16 + enc_size, 64);
    //@ open cryptogram(buffer + 16 + enc_size, 64, hmac_cs, ?hmac_cg);
    //@ assert hmac_cg == cg_hmac(?p3, ?c3, ?hmac_pay);
    
    // Decrypt
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key,
                       (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    //@ structure s = known_value(0, hmac_pay);
    //@ close decryption_pre(true, receiver, s, initial_request, enc_cs);
    if (aes_crypt_cfb128(&aes_context, AES_DECRYPT, (unsigned int) enc_size,
                           &iv_off, iv, buffer + 16, msg) != 0)
        abort();
    zeroize(iv, 16);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    //@ public_cryptogram(buffer + 16, enc_cg);
    //@ crypto_chars_to_chars(buffer, 16);
    //@ assert chars(buffer, 16 + enc_size, append(iv_cs, enc_cs));
    //@ assert crypto_chars(_, msg, enc_size, ?dec_cs);
    /*@ open decryption_post(true, receiver, s, initial_request,
                             ?wrong_key, sender, enc_id, dec_cs); @*/
    
    //Verify the hmac
    //@ assert crypto_chars(_, msg, size - 80, ?pay_cs);
    sha512_hmac(hmac_key, KEY_SIZE, msg,
                (unsigned int) enc_size, hmac, 0);
    //@ open cryptogram(hmac, 64, _, ?hmac_cg2);
    //@ assert hmac_cg2 == cg_hmac(sender, hmac_id, pay_cs);
    if (memcmp((void*) buffer + size - 64, hmac, 64) != 0) abort();
    //@ chars_for_cg_inj(hmac_cg, hmac_cg2);
    //@ assert col || hmac_cg == hmac_cg2;
    
    //@ public_crypto_chars(hmac, 64);
    //@ public_crypto_chars(buffer + size - 64, 64);
    /*@ if (wrong_key)
        {
          if (!col && !enc_and_hmac_public_key(sender, hmac_id, true))
          {
            assert !bad(sender);
            assert !bad(receiver);
            assert !enc_and_hmac_public_key(sender, enc_id, true);
            close exists(pair(nil, nil));
            close has_structure(hmac_pay, s);
            leak has_structure(hmac_pay, s);
          }
          decryption_with_wrong_key(msg, size - 80, s);
          chars_to_secret_crypto_chars(msg, enc_size);
        }
        else
        {
          if (!col)
          {
            assert hmac_cg == cg_hmac(sender, hmac_id, dec_cs);
            public_chars(buffer + size - 64, 64);
            open [_]enc_and_hmac_pub(enc_cg);
          }
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
  //@ close principal(receiver, _);
}

