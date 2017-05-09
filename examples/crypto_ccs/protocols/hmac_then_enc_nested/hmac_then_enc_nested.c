#include "hmac_then_enc_nested.h"

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void sender(char *enc_key1, char *enc_key2, char *hmac_key,
            char *msg, unsigned int msg_len)
/*@ requires [_]public_invar(hmac_then_enc_nested_pub) &*&
             principal(?sender, _) &*&
             [?f1]cryptogram(enc_key1, KEY_SIZE, ?enc_key_ccs1, ?enc_key_cg1) &*&
             [?f2]cryptogram(enc_key2, KEY_SIZE, ?enc_key_ccs2, ?enc_key_cg2) &*&
             [?f3]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
               enc_key_cg1 == cg_symmetric_key(sender, ?enc_id1) &*&
               enc_key_cg2 == cg_symmetric_key(sender, ?enc_id2) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               cg_info(enc_key_cg1) == hmac_id &*&
               cg_info(enc_key_cg2) == hmac_id &*&
               shared_with(sender, enc_id1) == shared_with(sender, hmac_id) &*&
               shared_with(sender, enc_id2) == shared_with(sender, hmac_id) &*&
             [?f4]crypto_chars(secret, msg, msg_len, ?msg_ccs) &*&
               MAX_SIZE >= msg_len &*& msg_len >= MINIMAL_STRING_SIZE &*&
               bad(sender) || bad(shared_with(sender, enc_id1)) ?
                 [_]public_ccs(msg_ccs)
               :
                 [_]memcmp_region(_, msg_ccs) &*&
                 true == send(sender, shared_with(sender, enc_id1), msg_ccs); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(enc_key1, KEY_SIZE, enc_key_ccs1, enc_key_cg1) &*&
             [f2]cryptogram(enc_key2, KEY_SIZE, enc_key_ccs2, enc_key_cg2) &*&
             [f3]cryptogram(hmac_key, KEY_SIZE, hmac_key_ccs, hmac_key_cg) &*&
             [f4]crypto_chars(secret, msg, msg_len, msg_ccs); @*/
{
  //@ open principal(sender, _);
  int socket;
  havege_state havege_state;

  unsigned int iv_off1 = 0;
  char iv1[16];
  unsigned int iv_off2 = 0;
  char iv2[16];
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
    //@ chars_to_crypto_chars(enc_msg, msg_len);
    memcpy(enc_msg, msg, msg_len);
    //@ assert crypto_chars(secret, enc_msg, msg_len, msg_ccs);
    // hmac
    /*@ if (bad(sender) || bad(shared_with(sender, enc_id1)))
          MEMCMP_CCS(msg_ccs)
    @*/
    sha512_hmac(hmac_key, KEY_SIZE, msg, msg_len, enc_msg + (int) msg_len, 0);
    //@ open cryptogram(enc_msg + msg_len, 64, ?hmac_ccs, ?hmac_cg);
    //@ close cryptogram(enc_msg  + msg_len, 64, hmac_ccs, hmac_cg);
    //@ close hmac_then_enc_nested_pub(hmac_cg);
    //@ leak hmac_then_enc_nested_pub(hmac_cg);
    //@ public_cryptogram(enc_msg  + msg_len, hmac_cg);
    //@ public_chars(enc_msg  + msg_len, 64);
    //@ assert [_]public_ccs(hmac_ccs);
    //@ chars_to_secret_crypto_chars(enc_msg  + msg_len, 64);
    //@ crypto_chars_join(enc_msg);
    //@ append_assoc(cs_to_ccs(identifier(0)), msg_ccs, hmac_ccs);
    //@ list<crypto_char> enc_msg_ccs = append(msg_ccs, hmac_ccs);
    //@ assert crypto_chars(secret, enc_msg, enc_len, enc_msg_ccs);

    int message_len = 2 * 16 + enc_len;
    char* temp = malloc(enc_len);
    if (temp == 0) abort();
    char* message = malloc(message_len);
    if (message == 0) abort();

    //@ close havege_state(&havege_state);
    havege_init(&havege_state);

    // IV stuff 1
    //@ close random_request(sender, 0, false);
    if (havege_random(&havege_state, iv1, 16) != 0) abort();
    //@ open cryptogram(iv1, 16, ?iv_ccs1, ?iv_cg1);
    //@ close hmac_then_enc_nested_pub(iv_cg1);
    //@ leak hmac_then_enc_nested_pub(iv_cg1);
    //@ chars_to_crypto_chars(message, 16);
    memcpy(message, iv1, 16);
    //@ close cryptogram(message, 16, iv_ccs1, iv_cg1);
    //@ public_cryptogram(message, iv_cg1);
    //@ assert chars(message, 16, ?iv_cs1);

    // encrypt 1
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key1,
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    if (aes_crypt_cfb128(&aes_context, AES_ENCRYPT, (unsigned int) enc_len,
                         &iv_off1, iv1, enc_msg, temp) != 0)
      abort();
    //@ open cryptogram(temp, enc_len, ?enc_ccs1, ?enc_cg1);
    zeroize(iv1, 16);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    zeroize(enc_msg, enc_len);

    // IV stuff 2
    //@ close random_request(sender, 0, false);
    if (havege_random(&havege_state, iv2, 16) != 0) abort();
    //@ open cryptogram(iv2, 16, ?iv_ccs2, ?iv_cg2);
    //@ close hmac_then_enc_nested_pub(iv_cg2);
    //@ leak hmac_then_enc_nested_pub(iv_cg2);
    //@ chars_to_crypto_chars(message + 16, 16);
    memcpy(message + 16, iv2, 16);
    //@ close cryptogram(message + 16, 16, iv_ccs2, iv_cg2);
    //@ public_cryptogram(message + 16, iv_cg2);
    //@ assert chars(message + 16, 16, ?iv_cs2);

    // encrypt 2
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key2,
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    if (aes_crypt_cfb128(&aes_context, AES_ENCRYPT, (unsigned int) enc_len,
                         &iv_off2, iv2, temp, message + 32) != 0)
      abort();
    //@ open cryptogram(message + 32, enc_len, ?enc_ccs2, ?enc_cg2);
    //@ close cryptogram(message + 32, enc_len, enc_ccs2, enc_cg2);
    zeroize(iv2, 16);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);

    havege_free(&havege_state);
    //@ open havege_state(&havege_state);

    /*@ if (hmac_then_enc_nested_public_key(sender, enc_id2, true))
        {
          assert true == hmac_then_enc_nested_public_key(sender, enc_id1, true);
          public_ccs_join(msg_ccs, hmac_ccs);
          close hmac_then_enc_nested_pub(enc_cg1);
          leak hmac_then_enc_nested_pub(enc_cg1);
          close cryptogram(temp, enc_len, enc_ccs1, enc_cg1);
          public_cryptogram(temp, enc_cg1);
          public_chars(temp, enc_len);
          chars_to_crypto_chars(temp, enc_len);
        }
        else
        {
          close hmac_then_enc_nested_pub_1(enc_cg1, msg_ccs, hmac_cg);
        }
    @*/
    //@ close hmac_then_enc_nested_pub(enc_cg2);
    //@ leak hmac_then_enc_nested_pub(enc_cg2);
    //@ public_cryptogram(message + 32, enc_cg2);
    //@ chars_join(message + 16);
    net_send(&socket, message, (unsigned int) message_len);
    free(enc_msg);
    zeroize(temp, enc_len);
    free(temp);
    free(message);
  }
  net_close(socket);
  //@ close principal(sender, _);
}

int receiver(char *enc_key1, char *enc_key2, char *hmac_key, char *msg)
/*@ requires [_]public_invar(hmac_then_enc_nested_pub) &*&
             [_]decryption_key_classifier(hmac_then_enc_nested_public_key) &*&
             principal(?receiver, _) &*&
             [?f1]cryptogram(enc_key1, KEY_SIZE, ?enc_key_ccs1, ?enc_key_cg1) &*&
             [?f2]cryptogram(enc_key2, KEY_SIZE, ?enc_key_ccs2, ?enc_key_cg2) &*&
             [?f3]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
               enc_key_cg1 == cg_symmetric_key(?sender, ?enc_id1) &*&
               enc_key_cg2 == cg_symmetric_key(sender, ?enc_id2) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               cg_info(enc_key_cg1) == hmac_id &*&
               cg_info(enc_key_cg2) == hmac_id &*&
               receiver == shared_with(sender, enc_id1) &*&
               receiver == shared_with(sender, enc_id2) &*&
               receiver == shared_with(sender, hmac_id) &*&
             chars(msg, MAX_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(enc_key1, KEY_SIZE, enc_key_ccs1, enc_key_cg1) &*&
             [f2]cryptogram(enc_key2, KEY_SIZE, enc_key_ccs2, enc_key_cg2) &*&
             [f3]cryptogram(hmac_key, KEY_SIZE, hmac_key_ccs, hmac_key_cg) &*&
             chars(msg + result, MAX_SIZE - result, _) &*&
             crypto_chars(secret, msg, result, ?msg_ccs) &*&
             col || bad(sender) || bad(receiver) ||
               send(sender, receiver, msg_ccs); @*/
{
  //@ open principal(receiver, _);
  int socket1;
  int socket2;

  int size;
  int enc_size;
  char hmac[64];
  unsigned int iv_off1 = 0;
  char iv1[16];
  unsigned int iv_off2 = 0;
  char iv2[16];
  aes_context aes_context;

  if(net_bind(&socket1, NULL, SERVER_PORT) != 0)
    abort();
  if(net_accept(socket1, &socket2, NULL) != 0)
    abort();
  if(net_set_block(socket2) != 0)
    abort();

  {
    int max_size = 2 * 16 + MAX_SIZE + 64;
    char *buffer = malloc (max_size); if (buffer == 0) abort();
    size = net_recv(&socket2, buffer, (unsigned int) max_size);
    if (size <= 2 * 16 + 64) abort();
    enc_size = size - 2 * 16;
    if (enc_size < MINIMAL_STRING_SIZE || enc_size > MAX_SIZE) abort();
    if (enc_size - 64 < MINIMAL_STRING_SIZE) abort();
    char *buffer_dec1 = malloc (enc_size); if (buffer_dec1 == 0) abort();
    char *buffer_dec2 = malloc (enc_size); if (buffer_dec2 == 0) abort();

    // IV stuff 1
    //@ chars_split(buffer, 16);
    //@ assert chars(buffer, 16, ?iv_cs1);
    //@ chars_to_crypto_chars(buffer, 16);
    //@ chars_to_crypto_chars(iv1, 16);
    memcpy(iv1, buffer, 16);
    //@ cs_to_ccs_crypto_chars(buffer, iv_cs1);
    //@ cs_to_ccs_crypto_chars(iv1, iv_cs1);
    //@ interpret_nonce(iv1, 16);
    //@ open cryptogram(iv1, 16, ?iv_ccs1, ?iv_cg1);

    // IV stuff 2
    //@ chars_split(buffer + 16, 16);
    //@ assert chars(buffer + 16, 16, ?iv_cs2);
    //@ chars_to_crypto_chars(buffer + 16, 16);
    //@ chars_to_crypto_chars(iv2, 16);
    memcpy(iv2, buffer + 16, 16);
    //@ cs_to_ccs_crypto_chars(buffer + 16, iv_cs2);
    //@ cs_to_ccs_crypto_chars(iv2, iv_cs2);
    //@ interpret_nonce(iv2, 16);
    //@ open cryptogram(iv2, 16, ?iv_ccs2, ?iv_cg2);

    //Decrypt 1
    //@ close aes_context(&aes_context);
    if (aes_setkey_enc(&aes_context, enc_key2,
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    //@ assert chars(buffer + 32, enc_size, ?enc_cs1);
    //@ interpret_encrypted(buffer + 32, enc_size);
    //@ assert cryptogram(buffer + 32, enc_size, ?enc_ccs1, ?enc_cg1);
    //@ assert enc_cg1 == cg_aes_encrypted(?p1, ?c1, ?pay_ccs1, ?ent1);
    //@ open [_]hmac_then_enc_nested_pub(enc_cg1);

    //@ structure s = cryptogram_with_payload(enc_size - 64, 64);
    //@ close decryption_pre(true, false, receiver, s, enc_ccs1);
    if (aes_crypt_cfb128(&aes_context, AES_DECRYPT, (unsigned int) enc_size,
                         &iv_off2, iv2, buffer + 32, buffer_dec1) != 0)
      abort();
    zeroize(iv2, 16);
    aes_free(&aes_context);
    //@ public_cryptogram(buffer + 32, enc_cg1);
    //@ assert crypto_chars(?kind1, buffer_dec1, enc_size, ?dec_ccs1);
    /*@ open decryption_post(true, ?garbage1, receiver,
                             s, sender, enc_id2, dec_ccs1); @*/
                             
    /*@ if (garbage1)
        {
          assert kind1 == normal;
          assert decryption_garbage(true, receiver, s,
                                    sender, enc_id2, dec_ccs1);
          close exists(pair(nil,nil));
          close decryption_pre(true, true, receiver, s, dec_ccs1);
          crypto_chars_to_chars(buffer_dec1, enc_size);
          interpret_encrypted(buffer_dec1, enc_size);
        }
        else
        {
          assert pay_ccs1 == dec_ccs1;
          if (hmac_then_enc_nested_public_key(p1, c1, true))
          {
            assert [_]public_ccs(pay_ccs1);
            public_crypto_chars(buffer_dec1, enc_size);
            interpret_encrypted(buffer_dec1, enc_size);
          }
          else
          {
            assert [_]hmac_then_enc_nested_pub_1(?enc_cg, ?msg_ccs, ?hmac_cg);
            close cryptogram(buffer_dec1, enc_size, dec_ccs1, enc_cg);
          }
          close decryption_pre(true, false, receiver, s, dec_ccs1);
        }
    @*/
    //@ assert cryptogram(buffer_dec1, enc_size, dec_ccs1, ?enc_cg2);
    //@ assert enc_cg2 == cg_aes_encrypted(?p2, ?c2, ?pay_ccs2, ?ent2);
    //@ assert decryption_pre(true, _, receiver, s, dec_ccs1);
    /*@ if (hmac_then_enc_nested_public_key(p1, c1, true) || garbage1)
          open [_]hmac_then_enc_nested_pub(enc_cg2); @*/
          
    //Decrypt 2
    if (aes_setkey_enc(&aes_context, enc_key1,
                        (unsigned int) (KEY_SIZE * 8)) != 0)
      abort();
    if (aes_crypt_cfb128(&aes_context, AES_DECRYPT, (unsigned int) enc_size,
                         &iv_off1, iv1, buffer_dec1, buffer_dec2) != 0)
      abort();
    zeroize(iv1, 16);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    //@ open cryptogram(buffer_dec1, enc_size, dec_ccs1, enc_cg2);
    //@ assert crypto_chars(?kind2, buffer_dec2, enc_size, ?dec_ccs2);
    /*@ open decryption_post(true, ?garbage2, receiver,
                             s, sender, enc_id1, dec_ccs2); @*/

    //Verify the hmac
    //@ public_ccs(buffer_dec2, enc_size);
    //@ crypto_chars_split(buffer_dec2, enc_size - 64);
    //@ assert crypto_chars(?kind, buffer_dec2, enc_size - 64, ?msg_ccs);
    //@ assert crypto_chars(kind, buffer_dec2 + enc_size - 64, 64, ?hmac_ccs);
    /*@ if (garbage2 || col || hmac_then_enc_nested_public_key(sender, enc_id2, true))
        {
          public_ccs_split(dec_ccs2, enc_size - 64);
          MEMCMP_CCS(msg_ccs)
        }
        else
        {
          assert [_]hmac_then_enc_nested_pub_1(?enc_cg, ?msg_ccs2, ?hmac_cg2);
          assert [_]memcmp_region(_, msg_ccs2);
          take_append(length(msg_ccs2), msg_ccs2, ccs_for_cg(hmac_cg2));
          take_append(length(msg_ccs), msg_ccs, ccs_for_cg(hmac_cg2));
          drop_append(length(msg_ccs2), msg_ccs2, ccs_for_cg(hmac_cg2));
          drop_append(length(msg_ccs), msg_ccs, ccs_for_cg(hmac_cg2));
        }
    @*/
    sha512_hmac(hmac_key, KEY_SIZE, buffer_dec2,
                (unsigned int) (enc_size - 64), hmac, 0);
    //@ open cryptogram(hmac, 64, ?hmac_ccs2, ?hmac_cg);
    /*@ if (col)
        {
          crypto_chars_to_chars(buffer_dec2 + enc_size - 64, 64);
          chars_to_crypto_chars(buffer_dec2 + enc_size - 64, 64);
          MEMCMP_PUB(buffer_dec2 + enc_size - 64)
        }
        else if (!garbage2)
        {
          assert !garbage1;
          if (bad(sender) || bad(receiver))
          {
            public_ccs_split(dec_ccs2, enc_size - 64);
            public_crypto_chars(buffer_dec2 + enc_size - 64, 64);
            chars_to_crypto_chars(buffer_dec2 + enc_size - 64, 64);
            MEMCMP_PUB(buffer_dec2 + enc_size - 64)
          }
          else
          {
            assert [_]hmac_then_enc_nested_pub_1(?enc_cg, ?msg_ccs2, ?hmac_cg2);
            MEMCMP_SEC(buffer_dec2 + enc_size - 64, hmac_cg2)
          }
        }
        else
        {
          MEMCMP_PUB(buffer_dec2 + enc_size - 64)
        }
    @*/
    //@ MEMCMP_SEC(hmac, hmac_cg)
    if (memcmp(hmac, (void*) buffer_dec2 + enc_size - 64, 64) != 0) abort();
    //@ assert hmac_ccs == hmac_ccs2;
    //@ chars_to_crypto_chars(msg, enc_size - 64);
    memcpy(msg, buffer_dec2, (unsigned int) enc_size - 64);

    /*@ if (garbage2)
        {
          close exists(hmac_cg);
          close exists(pair(msg_ccs, nil));
          close has_structure(dec_ccs2, s);
          leak has_structure(dec_ccs2, s);
          decryption_garbage(msg, enc_size, s);
          crypto_chars_to_chars(msg, enc_size - 64);
          chars_to_secret_crypto_chars(msg, enc_size - 64);
        }
    @*/
    /*@ if (!col && !bad(sender) && !bad(receiver))
        {
          open [_]hmac_then_enc_nested_pub(enc_cg1);
          assert p1 == sender && c1 == enc_id2;
          assert p2 == sender && c2 == enc_id1;

          assert [_]hmac_then_enc_nested_pub_1(?enc_cg3, ?msg_ccs2, ?hmac_cg2);
          ccs_for_cg_inj(enc_cg2, enc_cg3);
          assert pay_ccs2 == append(msg_ccs2, ccs_for_cg(hmac_cg2));
          take_append(length(pay_ccs2) - 64, msg_ccs2, ccs_for_cg(hmac_cg2));
          assert msg_ccs == msg_ccs2;
          ccs_for_cg_inj(hmac_cg, hmac_cg2);
        }
    @*/
    //@ chars_join(buffer);
    //@ chars_join(buffer);
    free(buffer);
    zeroize(hmac, 64);
    zeroize(buffer_dec1, enc_size);
    free(buffer_dec1);
    //@ assert crypto_chars(?k, buffer_dec2 + enc_size - 64, 64, _);
    /*@ if (k != kind) 
        {
          crypto_chars_to_chars(buffer_dec2 + enc_size - 64, 64);
          chars_to_secret_crypto_chars(buffer_dec2 + enc_size - 64, 64);
        }
    @*/
    //@ crypto_chars_join(buffer_dec2);
    zeroize(buffer_dec2, enc_size);
    free(buffer_dec2);
  }
  net_close(socket2);
  net_close(socket1);
  return enc_size - 64;
  //@ close principal(receiver, _);
}
