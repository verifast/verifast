#include "hmac_then_enc.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void sender(char *enc_key, char *hmac_key, char *msg, unsigned int msg_len)
/*@ requires [_]public_invar(hmac_then_enc_pub) &*&
             principal(?sender, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_ccs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
                 cg_info(enc_key_cg) == hmac_id &*&
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

  net_usleep(20000);
  if(net_connect(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();

  {
    aes_context aes_context;
    size_t enc_len = msg_len + 64;
    char* enc_msg = malloc(enc_len);
    if (enc_msg == 0) abort();

    // Copy message
    //@ chars__split(enc_msg, msg_len);
    crypto_memcpy(enc_msg, msg, msg_len);
    //@ assert crypto_chars(secret, enc_msg, msg_len, msg_ccs);

    // hmac
    /*@ if (bad(sender) || bad(shared_with(sender, enc_id)))
          MEMCMP_CCS(msg_ccs)
    @*/
    sha512_hmac(hmac_key, KEY_SIZE, msg, msg_len,
                enc_msg + (int) msg_len, 0);
    //@ assert cryptogram(enc_msg + msg_len, 64, ?hmac_ccs, ?hmac_cg);
    //@ open cryptogram(enc_msg + msg_len, 64, hmac_ccs, hmac_cg);
    //@ crypto_chars_join(enc_msg);
    //@ list<crypto_char> enc_msg_ccs = append(msg_ccs, hmac_ccs);
    //@ assert crypto_chars(secret, enc_msg, msg_len + 64, enc_msg_ccs);

    size_t message_len = 16U + enc_len;
    char* message = malloc(message_len);
    if (message == 0) abort();
     
    // IV stuff
    //@ close havege_state(&havege_state);
    havege_init(&havege_state);
    //@ close random_request(sender, 0, false);
    if (havege_random(&havege_state, iv, 16) != 0) abort();
    //@ open cryptogram(iv, 16, ?iv_ccs, ?iv_cg);
    //@ close hmac_then_enc_pub(iv_cg);
    //@ leak hmac_then_enc_pub(iv_cg);
    crypto_memcpy(message, iv, 16);
    //@ close cryptogram(message, 16, iv_ccs, iv_cg);
    //@ public_cryptogram(message, iv_cg);
    havege_free(&havege_state);
    //@ open havege_state(&havege_state);
    //@ assert chars(message, 16, ?iv_cs);

    // encrypt
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key,
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    if (aes_crypt_cfb128(&aes_context, AES_ENCRYPT, msg_len + 64,
                         &iv_off, iv, enc_msg, message + 16) != 0)
      abort();
    //@ assert cryptogram(message + 16, msg_len + 64, ?enc_cs, ?enc_cg);
    zeroize(iv, 16);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    
    //@ close hmac_then_enc_pub(hmac_cg);
    //@ leak hmac_then_enc_pub(hmac_cg);
    //@ take_append(msg_len, msg_ccs, hmac_ccs);
    //@ drop_append(msg_len, msg_ccs, hmac_ccs);
    //@ crypto_chars_split(enc_msg, msg_len);
    //@ close cryptogram(enc_msg + msg_len, 64, hmac_ccs, hmac_cg);
    //@ public_cryptogram(enc_msg + msg_len, hmac_cg);
    //@ public_chars(enc_msg + msg_len, 64);
    
    /*@ if (hmac_then_enc_public_key(sender, enc_id, true))
        {
          assert [_]public_ccs(msg_ccs);
          assert [_]public_ccs(hmac_ccs);
          public_crypto_chars(enc_msg, msg_len);
          assert chars(enc_msg, msg_len, ?msg_cs);
          assert chars(enc_msg + msg_len, 64, ?hmac_cs);
          cs_to_ccs_append(msg_cs, hmac_cs);
          chars_join(enc_msg);
          public_chars(enc_msg, msg_len + 64);
          chars_split(enc_msg, msg_len);
          chars_to_secret_crypto_chars(enc_msg, msg_len);
        }
        else
        {
          close hmac_then_enc_pub_1(msg_ccs, hmac_cg);
        }
    @*/
    //@ close hmac_then_enc_pub(enc_cg);
    //@ leak hmac_then_enc_pub(enc_cg);
    //@ public_cryptogram(message + 16, enc_cg);
    net_send(&socket, message, (unsigned int) message_len);
    //@ chars_to_secret_crypto_chars(enc_msg + msg_len, 64);
    //@ crypto_chars_join(enc_msg);
    zeroize(enc_msg, (int)enc_len);
    free(enc_msg);
    free(message);
  }
  net_close(socket);
  //@ close principal(sender, _);
}

int receiver(char *enc_key, char *hmac_key, char *msg)
/*@ requires [_]public_invar(hmac_then_enc_pub) &*&
             [_]decryption_key_classifier(hmac_then_enc_public_key) &*&
             principal(?receiver, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_ccs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(?sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
                 cg_info(enc_key_cg) == hmac_id &*&
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
  size_t enc_size;
  char hmac[64];
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
    size_t max_size = 20U + MAX_SIZE + 64;
    char *buffer = malloc (max_size); if (buffer == 0) abort();
    size = net_recv(&socket2, buffer, (unsigned int) max_size);
    if (size <= 16 + 64) abort();
    enc_size = (size_t)size - 16;
    if (enc_size < MINIMAL_STRING_SIZE || enc_size > MAX_SIZE) abort();
    if (enc_size - 64 < MINIMAL_STRING_SIZE) abort();
    char *buffer_dec = malloc (enc_size); if (buffer_dec == 0) abort();

    // IV stuff
    //@ chars_split(buffer, 16);
    //@ assert chars(buffer, 16, ?iv_cs);
    //@ chars_to_crypto_chars(buffer, 16);
    crypto_memcpy(iv, buffer, 16);
    //@ cs_to_ccs_crypto_chars(iv, iv_cs);
    //@ cs_to_ccs_crypto_chars(buffer, iv_cs);
    //@ interpret_nonce(iv, 16);
    //@ open cryptogram(iv, 16, ?iv_ccs, ?iv_cg);

    //Decrypt
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key,
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    //@ assert chars(buffer + 16, enc_size, ?enc_cs);
    //@ interpret_encrypted(buffer + 16, enc_size);
    //@ assert cryptogram(buffer + 16, enc_size, ?enc_ccs, ?enc_cg);
    //@ assert enc_cg == cg_aes_encrypted(?p2, ?c2, ?dec_ccs2, ?iv_cs2);

    //@ structure s = cryptogram_with_payload(enc_size - 64, 64);
    //@ close decryption_pre(true, false, receiver, s, enc_ccs);
    if (aes_crypt_cfb128(&aes_context, AES_DECRYPT, (unsigned int) enc_size,
                         &iv_off, iv, buffer + 16, buffer_dec) != 0)
      abort();
    zeroize(iv, 16);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    //@ public_cryptogram(buffer + 16, enc_cg);
    //@ open [_]hmac_then_enc_pub(enc_cg);
    //@ assert crypto_chars(_, buffer_dec, enc_size, ?dec_ccs);
    /*@ open decryption_post(true, ?garbage, receiver,
                             s, sender, enc_id, dec_ccs); @*/

    //@ crypto_chars_split(buffer_dec, enc_size - 64);
    
    //Verify the hmac
    //@ assert crypto_chars(_, buffer_dec, enc_size - 64, ?pay_ccs);
    //@ public_ccs(buffer_dec, enc_size - 64);
    /*@ if (garbage || col || hmac_then_enc_public_key(sender, enc_id, true))
        {
          if (!garbage && !col)
            public_ccs_split(dec_ccs, enc_size - 64);
          MEMCMP_CCS(pay_ccs)
        }
        else
        {
          assert [_]hmac_then_enc_pub_1(?msg_ccs, ?hmac_cg2);
          assert [_]memcmp_region(_, msg_ccs);
          take_append(enc_size - 64, msg_ccs, ccs_for_cg(hmac_cg2));
          take_append(enc_size - 64, pay_ccs, drop(enc_size - 64, dec_ccs));
        }
    @*/
    sha512_hmac(hmac_key, KEY_SIZE, buffer_dec,
                (unsigned int) (enc_size - 64), hmac, 0);
                
    //@ open cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
    //@ crypto_chars_distinct(hmac, (void*) buffer_dec + enc_size - 64);
    /*@ if (col)
        {
          crypto_chars_to_chars(buffer_dec + enc_size - 64, 64);
          chars_to_crypto_chars(buffer_dec + enc_size - 64, 64);
          MEMCMP_PUB((void*) buffer_dec + enc_size - 64)
        }
        else if (!garbage)
        {
          if (bad(sender) || bad(receiver))
          {
            public_ccs_split(dec_ccs, enc_size - 64);
            public_crypto_chars(buffer_dec + enc_size - 64, 64);
            chars_to_crypto_chars(buffer_dec + enc_size - 64, 64);
            MEMCMP_PUB((void*) buffer_dec + enc_size - 64)
          }
          else
          {
            assert [_]hmac_then_enc_pub_1(?msg_ccs, ?hmac_cg2);
            drop_append(length(pay_ccs), msg_ccs, ccs_for_cg(hmac_cg2));
            drop_append(length(pay_ccs), pay_ccs, ccs_for_cg(hmac_cg));
            MEMCMP_SEC((void*) buffer_dec + enc_size - 64, hmac_cg2)
          }
        }
        else
        {
          MEMCMP_PUB((void*) buffer_dec + enc_size - 64)
        }
    @*/
    //@ MEMCMP_SEC(hmac, hmac_cg)
    if (crypto_memcmp(hmac, (void*) buffer_dec + enc_size - 64, 64) != 0) abort();
    crypto_memcpy(msg, buffer_dec, (unsigned int) enc_size - 64);
    /*@ if (garbage)
        {
          close exists(hmac_cg);
          close exists(pair(pay_ccs, nil));
          close has_structure(dec_ccs, s);
          leak has_structure(dec_ccs, s);
          decryption_garbage(msg, enc_size, s);
        }
    @*/
    /*@ if (!col && !bad(sender) && !bad(receiver))
        {
          assert [_]hmac_then_enc_pub_1(?msg_ccs, ?hmac_cg2);
          ccs_for_cg_inj(hmac_cg, hmac_cg2);
          assert pay_ccs == msg_ccs;        }
    @*/
    
    //@ chars_join(buffer);
    free(buffer);
    zeroize(hmac, 64);
    zeroize(buffer_dec, (int)enc_size - 64);
    zeroize(buffer_dec + enc_size - 64, 64);
    //@ chars_join(buffer_dec);
    free(buffer_dec);
  }
  net_close(socket2);
  net_close(socket1);
  return (int)enc_size - 64;
  //@ close principal(receiver, _);
}
