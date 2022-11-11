#include "enc_and_hmac.h"

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void sender(char *enc_key, char *hmac_key, char *msg, unsigned int msg_len)
/*@ requires [_]public_invar(enc_and_hmac_pub) &*&
             principal(?sender, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_ccs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               shared_with(sender, enc_id) == shared_with(sender, hmac_id) &*&
             [?f3]crypto_chars(secret, msg, msg_len, ?msg_ccs) &*&
               MAX_SIZE >= msg_len &*& msg_len >= MINIMAL_STRING_SIZE &*&
               bad(sender) || bad(shared_with(sender, enc_id)) ?
                 [_]public_ccs(msg_ccs)
               :
                 [_]memcmp_region(_, msg_ccs) &*&
                 true == send(sender, shared_with(sender, enc_id), msg_ccs); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(enc_key, KEY_SIZE, enc_key_ccs, enc_key_cg) &*&
             [f2]cryptogram(hmac_key, KEY_SIZE, hmac_key_ccs, hmac_key_cg) &*&
             [f3]crypto_chars(secret, msg, msg_len, msg_ccs); @*/
{
  //@ open principal(sender, _);
  int socket;
  havege_state havege_state;

  size_t iv_off = 0;
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
    char* message = malloc((size_t)message_len);
    if (message == 0) abort();

    // IV stuff
    //@ close havege_state(&havege_state);
    havege_init(&havege_state);
    //@ close random_request(sender, 0, false);
    if (havege_random(&havege_state, iv, 16) != 0) abort();
    //@ open cryptogram(iv, 16, ?iv_ccs, ?iv_cg);
    crypto_memcpy(message, iv, 16);
    //@ close cryptogram(message, 16, iv_ccs, iv_cg);
    //@ close enc_and_hmac_pub(iv_cg);
    //@ leak enc_and_hmac_pub(iv_cg);
    //@ public_cryptogram(message, iv_cg);
    havege_free(&havege_state);
    //@ open havege_state(&havege_state);
    //@ assert chars(message, 16, ?iv_cs);
    
    // encrypt
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key,
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    if (aes_crypt_cfb128(&aes_context, AES_ENCRYPT, msg_len,
                         &iv_off, iv, msg, message + 16) != 0)
      abort();
    zeroize(iv, 16);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    
    //@ assert cryptogram(message + 16, msg_len, ?enc_ccs, ?enc_cg);
    //@ close enc_and_hmac_pub(enc_cg);
    //@ leak enc_and_hmac_pub(enc_cg);
    //@ public_cryptogram(message + 16, enc_cg);
    //@ assert chars(message + 16, msg_len, ?enc_cs);
    //@ chars_join(message);
    //@ assert enc_cg == cg_aes_encrypted(sender, enc_id, msg_ccs, iv_ccs);
    //@ assert chars(message, 16 + msg_len, append(iv_cs, enc_cs));
    //@ chars_to_crypto_chars(message, 16 + msg_len);
    //@ cs_to_ccs_append(iv_cs, enc_cs);
    //@ assert crypto_chars(normal, message, 16 + msg_len, append(iv_ccs, enc_ccs));
    //@ assert append(iv_ccs, enc_ccs) == cs_to_ccs(append(iv_cs, enc_cs));
    
    // hmac
    /*@ if (bad(sender) || bad(shared_with(sender, enc_id)))
          MEMCMP_CCS(msg_ccs)
    @*/
    sha512_hmac(hmac_key, KEY_SIZE, msg, (unsigned int) (msg_len),
                message + 16 + (int) msg_len, 0);
    //@ assert cryptogram(message + 16 + msg_len, 64, ?hmac_ccs, ?hmac_cg);
    //@ assert hmac_cg == cg_sha512_hmac(sender, hmac_id, msg_ccs);
    //@ close enc_and_hmac_pub(hmac_cg);
    //@ leak enc_and_hmac_pub(hmac_cg);
    //@ public_cryptogram(message + 16 + msg_len, hmac_cg);
    //@ assert chars(message + 16 + msg_len, 64, ?hmac_cs);
    //@ cs_to_ccs_crypto_chars(message, append(iv_cs, enc_cs));
    //@ chars_join(message);
    //@ append_assoc(iv_cs, enc_cs, hmac_cs);
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
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_ccs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(?sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               receiver == shared_with(sender, enc_id) &*&
               receiver == shared_with(sender, hmac_id) &*&
             chars_(msg, MAX_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(enc_key, KEY_SIZE, enc_key_ccs, enc_key_cg) &*&
             [f2]cryptogram(hmac_key, KEY_SIZE, hmac_key_ccs, hmac_key_cg) &*&
             chars_(msg + result, MAX_SIZE - result, _) &*&
             crypto_chars(secret, msg, result, ?msg_ccs) &*&
             [_]memcmp_region(_, msg_ccs) &*&
             col || bad(sender) || bad(receiver) ||
               send(sender, receiver , msg_ccs); @*/
{
  //@ open principal(receiver, _);
  int socket1;
  int socket2;

  int size;
  int enc_size;
  char hmac[64];
  unsigned int temp;
  size_t iv_off = 0;
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
    char *buffer = malloc ((size_t)max_size); if (buffer == 0) abort();
    size = net_recv(&socket2, buffer, (unsigned int) max_size);
    if (size <= 16 + 64) abort();
    enc_size = size - 16 - 64;
    if (enc_size < MINIMAL_STRING_SIZE) abort();

    // Interpret message
    //@ chars_split(buffer, 16);
    //@ assert chars(buffer, 16, ?iv_cs);
    //@ chars_to_crypto_chars(buffer, 16);
    crypto_memcpy(iv, buffer, 16);
    //@ cs_to_ccs_crypto_chars(iv, iv_cs);
    //@ interpret_nonce(iv, 16);
    //@ open cryptogram(iv, 16, ?iv_ccs, ?iv_cg);

    //@ assert chars(buffer + 16, enc_size, ?enc_cs);
    //@ interpret_encrypted(buffer + 16, enc_size);
    //@ open cryptogram(buffer + 16, enc_size, ?enc_ccs, ?enc_cg);
    //@ close cryptogram(buffer + 16, enc_size, enc_ccs, enc_cg);
    //@ assert enc_cg == cg_aes_encrypted(?p2, ?c2, ?dec_ccs2, ?iv_ccs2);
    
    //@ assert chars(buffer + 16 + enc_size, 64, ?hmac_cs);
    //@ interpret_hmac(buffer + 16 + enc_size, 64);
    //@ open cryptogram(buffer + 16 + enc_size, 64, ?hmac_ccs, ?hmac_cg);
    //@ assert hmac_cg == cg_sha512_hmac(?p3, ?c3, ?hmac_pay);
    
    // Decrypt
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key,
                       (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    //@ structure s = known_value(0, hmac_pay);
    //@ close decryption_pre(true, false, receiver, s, enc_ccs);
    if (aes_crypt_cfb128(&aes_context, AES_DECRYPT, (unsigned int) enc_size,
                           &iv_off, iv, buffer + 16, msg) != 0)
        abort();
    zeroize(iv, 16);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    //@ open [_]enc_and_hmac_pub(enc_cg);
    //@ public_cryptogram(buffer + 16, enc_cg);
    //@ cs_to_ccs_crypto_chars(buffer, iv_cs);
    //@ assert chars(buffer + 16, enc_size, ?enc_cs');
    //@ cs_to_ccs_inj(enc_cs, enc_cs');
    //@ chars_join(buffer);
    //@ assert chars(buffer, 16 + enc_size, append(iv_cs, enc_cs));
    //@ assert crypto_chars(_, msg, enc_size, ?dec_ccs);
    /*@ open decryption_post(true, ?garbage, receiver,
                             s, sender, enc_id, dec_ccs); @*/
    
    //Verify the hmac
    //@ assert crypto_chars(?kind, msg, size - 80, ?pay_ccs);
    //@ public_ccs(msg, size - 80);
    /*@ if (garbage || col || enc_and_hmac_public_key(sender, enc_id, true))
          MEMCMP_CCS(pay_ccs)
    @*/
    sha512_hmac(hmac_key, KEY_SIZE, msg,
                (unsigned int) enc_size, hmac, 0);
    //@ open cryptogram(hmac, 64, ?hmac_cs2, ?hmac_cg2);
    //@ assert hmac_cg2 == cg_sha512_hmac(sender, hmac_id, pay_ccs);
    //@ public_crypto_chars(buffer + size - 64, 64);
    //@ chars_to_crypto_chars(buffer + size - 64, 64);
    //@ MEMCMP_SEC(hmac, hmac_cg2)
    //@ MEMCMP_PUB((void*) buffer + size - 64)
    if (crypto_memcmp((void*) buffer + size - 64, hmac, 64) != 0) abort();   
    //@ ccs_for_cg_inj(hmac_cg, hmac_cg2);
    //@ assert col || hmac_cg == hmac_cg2;
    //@ public_crypto_chars(hmac, 64);
    //@ crypto_chars_to_chars(buffer + size - 64, 64);
    
    /*@ if (garbage)
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
          else
          {
            crypto_chars_to_chars(msg, enc_size);
            chars_to_secret_crypto_chars(msg, enc_size);
          }
          decryption_garbage(msg, size - 80, s);
        }
        else
        {
          if (!col)
          {
            assert hmac_cg == cg_sha512_hmac(sender, hmac_id, dec_ccs);
            public_chars(buffer + size - 64, 64);
            open [_]enc_and_hmac_pub(enc_cg);
          }
       }
    @*/
    //@ chars_join(buffer);
    free(buffer);
  }
  net_close(socket2);
  net_close(socket1);
  return enc_size;
  //@ close principal(receiver, _);
}

