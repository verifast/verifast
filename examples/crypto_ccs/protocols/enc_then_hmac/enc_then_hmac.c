#include "enc_then_hmac.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void sender(char *enc_key, char *hmac_key, char *msg, unsigned int msg_len)
/*@ requires [_]public_invar(enc_then_hmac_pub) &*&
             principal(?sender, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_ccs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
                 cg_info(hmac_key_cg) == enc_id &*&
               shared_with(sender, enc_id) == shared_with(sender, hmac_id) &*&
             [?f3]crypto_chars(secret, msg, msg_len, ?msg_ccs) &*&
               MAX_SIZE >= msg_len &*& msg_len >= MINIMAL_STRING_SIZE &*&
               bad(sender) || bad(shared_with(sender, enc_id)) ?
                 [_]public_ccs(msg_ccs)
               :
                 true == send(sender, shared_with(sender, enc_id), msg_ccs); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(enc_key, KEY_SIZE, enc_key_ccs, enc_key_cg) &*&
             [f2]cryptogram(hmac_key, KEY_SIZE, hmac_key_ccs, hmac_key_cg) &*&
             [f3]crypto_chars(secret, msg, msg_len, msg_ccs); @*/
{
  //@ open principal(sender, _);
  int socket;
  havege_state havege_state;

  char iv[16];
  size_t iv_off = 0;
  char hmac[64];
  aes_context aes_context;
  
  net_usleep(20000);
  if(net_connect(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();
  {
    size_t message_len = 16U + msg_len + 64;
    char* message = malloc(message_len);
    if (message == 0) abort();

    // IV stuff
    //@ close havege_state(&havege_state);
    havege_init(&havege_state);
    //@ close random_request(sender, 0, false);
    if (havege_random(&havege_state, iv, 16) != 0) abort();
    //@ open cryptogram(iv, 16, ?iv_ccs, ?iv_cg);
    //@ close enc_then_hmac_pub(iv_cg);
    //@ leak enc_then_hmac_pub(iv_cg);
    crypto_memcpy(message, iv, 16);
    //@ close cryptogram(message, 16, iv_ccs, iv_cg);
    //@ public_cryptogram(message, iv_cg);
    //@ assert chars(message, 16, ?iv_cs);
    //@ public_chars(message, 16);
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
    //@ open cryptogram(message + 16, msg_len, ?enc_ccs, ?enc_cg);
    //@ close cryptogram(message + 16, msg_len, enc_ccs, enc_cg);
    //@ close enc_then_hmac_pub(enc_cg);
    //@ leak enc_then_hmac_pub(enc_cg);
    //@ public_cryptogram(message + 16, enc_cg);
    //@ assert chars(message + 16, msg_len, ?enc_cs);
    //@ public_chars(message + 16, msg_len);
    //@ assert chars(message, 16 + msg_len, append(iv_cs, enc_cs));
    //@ assert enc_cg == cg_aes_encrypted(sender, enc_id, msg_ccs, iv_ccs);
    zeroize(iv, 16);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    
    // hmac
    //@ chars_to_crypto_chars(message, 16 + msg_len);
    //@ MEMCMP_PUB(message)
    sha512_hmac(hmac_key, KEY_SIZE, message,
                (unsigned int) (16 + (int) msg_len),
                message + 16 + (int) msg_len, 0);
    //@ assert cryptogram(message + 16 + msg_len, 64, ?hmac_ccs, ?hmac_cg);
    //@ cs_to_ccs_append(iv_cs, enc_cs);
    //@ assert hmac_cg == cg_sha512_hmac(sender, hmac_id, append(iv_ccs, enc_ccs));
    /*@ if (!col && !enc_then_hmac_public_key(sender, enc_id, true))
          close enc_then_hmac_pub_1(enc_id, msg_ccs, iv_ccs); @*/
    /*@ if (col || enc_then_hmac_public_key(sender, enc_id, true))
        { 
          assert [_]public_ccs(iv_ccs);
          assert [_]public_ccs(enc_ccs);
          public_ccs_join(iv_ccs, enc_ccs);
        }
    @*/
    //@ close enc_then_hmac_pub(hmac_cg);
    //@ leak enc_then_hmac_pub(hmac_cg);
    //@ public_cryptogram(message + 16 + msg_len, hmac_cg);
    //@ assert chars(message + 16 + msg_len, 64, ?hmac_cs);
    //@ append_assoc(iv_ccs, enc_ccs, hmac_ccs);
    //@ append_assoc(iv_cs, enc_cs, hmac_cs);
    //@ cs_to_ccs_crypto_chars(message, append(iv_cs, enc_cs));
    /*@ assert chars(message, message_len,
                     append(iv_cs, append(enc_cs, hmac_cs))); @*/
    net_send(&socket, message, (unsigned int) message_len);
    
    free(message);
  }
  net_close(socket);
  //@ close principal(sender, _);
}

int receiver(char *enc_key, char *hmac_key, char *msg)
/*@ requires [_]public_invar(enc_then_hmac_pub) &*&
             [_]decryption_key_classifier(enc_then_hmac_public_key) &*&
             principal(?receiver, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_ccs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(?sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
                 cg_info(hmac_key_cg) == enc_id &*&
               receiver == shared_with(sender, enc_id) &*&
               receiver == shared_with(sender, hmac_id) &*&
             chars_(msg, MAX_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(enc_key, KEY_SIZE, enc_key_ccs, enc_key_cg) &*&
             [f2]cryptogram(hmac_key, KEY_SIZE, hmac_key_ccs, hmac_key_cg) &*&
             chars_(msg + result, MAX_SIZE - result, _) &*&
             crypto_chars(?kind, msg, result, ?msg_ccs) &*&
             col || bad(sender) || bad(receiver) ||
               (kind == secret && send(sender, receiver, msg_ccs)); @*/
{
  //@ open principal(receiver, _);
  int socket1;
  int socket2;

  int size;
  int enc_size;
  char iv[16];
  size_t iv_off = 0;
  char hmac[64];
  aes_context aes_context;

  if(net_bind(&socket1, NULL, SERVER_PORT) != 0)
    abort();
  if(net_accept(socket1, &socket2, NULL) != 0)
    abort();
  if(net_set_block(socket2) != 0)
    abort();

  {
    size_t max_size = 16U + MAX_SIZE + 64;
    char *buffer = malloc (max_size); if (buffer == 0) abort();
    size = net_recv(&socket2, buffer, (unsigned int) max_size);
    if (size <= 16 + 64) abort();
    enc_size = size - 16 - 64;
    if (enc_size < MINIMAL_STRING_SIZE) abort();

    //Verify the hmac
    //@ chars_split(buffer, size - 64);
    //@ public_chars(buffer + size - 64, 64);
    //@ assert chars(buffer + size - 64, 64, ?hmac_cs);
    //@ assert chars(buffer, size - 64, ?pay_cs);
    //@ chars_to_crypto_chars(buffer, size - 64);
    //@ MEMCMP_PUB(buffer)
    sha512_hmac(hmac_key, KEY_SIZE, buffer,
                (unsigned int) (size - 64), hmac, 0);
    //@ open cryptogram(hmac, 64, ?hmac_ccs, ?hmac_cg);
    //@ chars_to_crypto_chars((void*) buffer + size - 64, 64);
    //@ MEMCMP_SEC(hmac, hmac_cg)
    //@ MEMCMP_PUB((void*) buffer + size - 64)
    if (crypto_memcmp((void*) buffer + size - 64, hmac, 64) != 0) abort();
    /*@ if (!col) 
        {
          public_ccs_cg(hmac_cg);
          public_crypto_chars(hmac, 64);
        }
        else
        {
          crypto_chars_to_chars(hmac, 64);
        }
    @*/

    // IV stuff
    //@ cs_to_ccs_crypto_chars(buffer, pay_cs);
    //@ chars_split(buffer, 16);
    //@ assert chars(buffer, 16, ?iv_cs);
    //@ chars_to_crypto_chars(buffer, 16);
    //@ assert crypto_chars(normal, buffer, 16, ?iv_ccs);
    crypto_memcpy(iv, buffer, 16);
    //@ cs_to_ccs_crypto_chars(iv, iv_cs);
    //@ interpret_nonce(iv, 16);
    //@ open cryptogram(iv, 16, iv_ccs, ?iv_cg);

    //Decrypt
    //@ assert chars(buffer + 16, enc_size, ?enc_cs);
    //@ interpret_encrypted(buffer + 16, enc_size);
    //@ open cryptogram(buffer + 16, enc_size, ?enc_ccs, ?enc_cg);
    //@ close cryptogram(buffer + 16, enc_size, enc_ccs, enc_cg);
    //@ assert enc_cg == cg_aes_encrypted(?p2, ?c2, ?dec_ccs2, ?iv_ccs2);
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key,
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    //@ structure s = known_value(0, dec_ccs2);
    //@ close decryption_pre(true, false, receiver, s, enc_ccs);
    if (aes_crypt_cfb128(&aes_context, AES_DECRYPT, (unsigned int) enc_size,
                         &iv_off, iv, buffer + 16, msg) != 0)
      abort();
    //@ assert pay_cs == append(iv_cs, enc_cs);
    //@ cs_to_ccs_append(iv_cs, enc_cs);
    zeroize(iv, 16);
    aes_free(&aes_context);
    
    //@ open aes_context(&aes_context);
    //@ public_cg_ccs(enc_cg);
    //@ public_cryptogram(buffer + 16, enc_cg);
    /*@ open decryption_post(true, ?garbage, receiver,
                             s, sender, enc_id, ?dec_ccs); @*/
    /*@ if (!col)
        {
          open [_]enc_then_hmac_pub(hmac_cg);
          open [_]enc_then_hmac_pub(enc_cg);
          if (!enc_then_hmac_public_key(sender, enc_id, true))
          {
            assert [_]enc_then_hmac_pub_1(?id, ?dec_ccs3, ?ent);
            cryptogram enc_cg3 = cg_aes_encrypted(sender, id, dec_ccs3, ent);
            take_append(16, iv_ccs, ccs_for_cg(enc_cg));
            take_append(16, ent, ccs_for_cg(enc_cg3));
            assert ent == iv_ccs;
            drop_append(16, iv_ccs, ccs_for_cg(enc_cg));
            drop_append(16, ent, ccs_for_cg(enc_cg3));
            assert ccs_for_cg(enc_cg) == ccs_for_cg(enc_cg3);
            ccs_for_cg_inj(enc_cg, enc_cg3);
            assert dec_ccs2 == dec_ccs3;
            close exists(pair(nil, nil));
            close has_structure(dec_ccs2, s);
            leak has_structure(dec_ccs2, s);
          }
        }
        else
        {
          crypto_chars_to_chars(msg, enc_size);
          chars_to_secret_crypto_chars(msg, enc_size);
        }
    @*/
    //@ if (garbage) decryption_garbage(msg, enc_size, s);
    //@ crypto_chars_to_chars(buffer, 16);
    //@ crypto_chars_to_chars(buffer + size - 64, 64);
    //@ chars_join(buffer);
    //@ chars_join(buffer);
    free(buffer);
  }
  net_close(socket2);
  net_close(socket1);
  return enc_size;
  //@ close principal(receiver, _);
}
