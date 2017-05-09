#include "hmac_then_enc_tagged.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void sender(char *enc_key, char *hmac_key, char *msg, unsigned int msg_len)
/*@ requires [_]public_invar(hmac_then_enc_tagged_pub) &*&
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
    int enc_len = ID_SIZE + (int) msg_len + 64;
    char* enc_msg = malloc(enc_len);
    if (enc_msg == 0) abort();

    // Copy message
    write_identifier(enc_msg, 0);
    //@ assert crypto_chars(normal, enc_msg, ID_SIZE, cs_to_ccs(identifier(0)));
    //@ assert [_]public_ccs(cs_to_ccs(identifier(0)));
    //@ crypto_chars_to_chars(enc_msg, ID_SIZE);
    //@ chars_to_secret_crypto_chars(enc_msg, ID_SIZE);
    //@ chars_to_secret_crypto_chars(enc_msg + ID_SIZE, msg_len);
    memcpy(enc_msg + ID_SIZE, msg, msg_len);
    //@ assert crypto_chars(secret, enc_msg + ID_SIZE, msg_len, msg_ccs);
    //@ crypto_chars_join(enc_msg);
    // hmac
    /*@ if (bad(sender) || bad(shared_with(sender, enc_id)))
          MEMCMP_CCS(msg_ccs)
    @*/
    sha512_hmac(hmac_key, KEY_SIZE, msg, msg_len,
                enc_msg + ID_SIZE + (int) msg_len, 0);
    //@ open cryptogram(enc_msg + ID_SIZE + msg_len, 64, ?hmac_ccs, ?hmac_cg);
    //@ close cryptogram(enc_msg + ID_SIZE + msg_len, 64, hmac_ccs, hmac_cg);
    //@ close hmac_then_enc_tagged_pub(hmac_cg);
    //@ leak hmac_then_enc_tagged_pub(hmac_cg);
    //@ public_cryptogram(enc_msg + ID_SIZE + msg_len, hmac_cg);
    //@ public_chars(enc_msg + ID_SIZE + msg_len, 64);
    //@ assert [_]public_ccs(hmac_ccs);
    //@ chars_to_secret_crypto_chars(enc_msg + ID_SIZE + msg_len, 64);
    //@ crypto_chars_join(enc_msg);
    //@ append_assoc(cs_to_ccs(identifier(0)), msg_ccs, hmac_ccs);
    /*@ list<crypto_char> enc_msg_ccs = append(cs_to_ccs(identifier(0)), 
                                              append(msg_ccs, hmac_ccs)); @*/
    //@ assert crypto_chars(secret, enc_msg, enc_len, enc_msg_ccs);
    
    int message_len = 16 + enc_len;
    char* message = malloc(message_len);
    if (message == 0) abort();
     
    // IV stuff
    //@ close havege_state(&havege_state);
    havege_init(&havege_state);
    //@ close random_request(sender, 0, false);
    if (havege_random(&havege_state, iv, 16) != 0) abort();
    //@ open cryptogram(iv, 16, ?iv_ccs, ?iv_cg);
    //@ close hmac_then_enc_tagged_pub(iv_cg);
    //@ leak hmac_then_enc_tagged_pub(iv_cg);
    //@ chars_to_secret_crypto_chars(message, 16);
    memcpy(message, iv, 16);
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
    if (aes_crypt_cfb128(&aes_context, AES_ENCRYPT, (unsigned int) enc_len,
                         &iv_off, iv, enc_msg, message + 16) != 0)
      abort();
    //@ open cryptogram(message + 16, enc_len, ?enc_cs, ?enc_cg);
    //@ close cryptogram(message + 16, enc_len, enc_cs, enc_cg);
    zeroize(iv, 16);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    zeroize(enc_msg, enc_len);
    
    /*@ if (hmac_then_enc_tagged_public_key(sender, enc_id, true))
        {
          public_ccs_join(cs_to_ccs(identifier(0)), msg_ccs);
          public_ccs_join(append(cs_to_ccs(identifier(0)), msg_ccs), 
                          hmac_ccs);
        }
        else
        {
          close hmac_then_enc_tagged_pub_1(msg_ccs, hmac_cg);
        }
    @*/
    //@ close hmac_then_enc_tagged_pub(enc_cg);
    //@ leak hmac_then_enc_tagged_pub(enc_cg);
    //@ public_cryptogram(message + 16, enc_cg);
    net_send(&socket, message, (unsigned int) message_len);
    free(enc_msg);
    free(message);
  }
  net_close(socket);
  //@ close principal(sender, _);
}

int receiver(char *enc_key, char *hmac_key, char *msg)
/*@ requires [_]public_invar(hmac_then_enc_tagged_pub) &*&
             [_]decryption_key_classifier(hmac_then_enc_tagged_public_key) &*&
             principal(?receiver, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_ccs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(?sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
                 cg_info(enc_key_cg) == hmac_id &*&
               receiver == shared_with(sender, enc_id) &*&
               receiver == shared_with(sender, hmac_id) &*&
             chars(msg, MAX_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(enc_key, KEY_SIZE, enc_key_ccs, enc_key_cg) &*&
             [f2]cryptogram(hmac_key, KEY_SIZE, hmac_key_ccs, hmac_key_cg) &*&
             chars(msg + result, MAX_SIZE - result, _) &*&
             crypto_chars(_, msg, result, ?msg_ccs) &*&
             col || bad(sender) || bad(receiver) ||
               send(sender, receiver, msg_ccs); @*/
{
  //@ open principal(receiver, _);
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
    if (size <= 16 + ID_SIZE + 64) abort();
    enc_size = size - 16;
    if (enc_size < MINIMAL_STRING_SIZE || enc_size > MAX_SIZE) abort();
    if (enc_size - ID_SIZE - 64 < MINIMAL_STRING_SIZE) abort();
    char *buffer_dec = malloc (enc_size); if (buffer_dec == 0) abort();

    // IV stuff
    //@ chars_split(buffer, 16);
    //@ assert chars(buffer, 16, ?iv_cs);
    //@ chars_to_crypto_chars(buffer, 16);
    //@ chars_to_secret_crypto_chars(iv, 16);
    memcpy(iv, buffer, 16);
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
    //@ assert enc_cg == cg_aes_encrypted(?p2, ?c2, ?dec_ccs2, ?iv_ccs2);
    //@ open [_]hmac_then_enc_tagged_pub(enc_cg);

    //@ structure s = known_value(0, cs_to_ccs(identifier(0)));
    //@ close decryption_pre(true, false, receiver, s, enc_ccs);
    if (aes_crypt_cfb128(&aes_context, AES_DECRYPT, (unsigned int) enc_size,
                         &iv_off, iv, buffer + 16, buffer_dec) != 0)
      abort();
    zeroize(iv, 16);
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    //@ public_cryptogram(buffer + 16, enc_cg);
    /*@ open decryption_post(true, ?garbage, receiver,
                             s, sender, enc_id, ?dec_ccs); @*/
    //@ assert crypto_chars(?kind, buffer_dec, enc_size, dec_ccs);
    //@ public_ccs(buffer_dec, enc_size);
    //@ crypto_chars_split(buffer_dec, ID_SIZE);
    //@ assert crypto_chars(kind, buffer_dec, ID_SIZE, ?id_ccs);
    //@ assert crypto_chars(kind, buffer_dec + ID_SIZE, enc_size - ID_SIZE, ?rest_ccs);
    //@ take_append(ID_SIZE, id_ccs, rest_ccs);
    //@ drop_append(ID_SIZE, id_ccs, rest_ccs);
    //@ crypto_chars_split(buffer_dec + ID_SIZE, enc_size - ID_SIZE - 64);
    //@ assert crypto_chars(_, buffer_dec + ID_SIZE, enc_size - ID_SIZE - 64, ?pay_ccs);
    //@ assert crypto_chars(_, buffer_dec + enc_size - 64, 64, ?hmac_ccs);
    //@ assert rest_ccs == append(pay_ccs, hmac_ccs);

    /*@ if (col || garbage || bad(sender) || bad(receiver))
        {
          public_ccs_split(dec_ccs, ID_SIZE);
          public_ccs_split(rest_ccs, enc_size - ID_SIZE - 64);
          public_crypto_chars(buffer_dec, ID_SIZE);
          public_crypto_chars(buffer_dec + enc_size - 64, 64);
          chars_to_crypto_chars(buffer_dec + enc_size - 64, 64);
          MEMCMP_CCS(pay_ccs)
          MEMCMP_PUB(buffer_dec + enc_size - 64)
        }
        else
        {
          assert [_]hmac_then_enc_tagged_pub_1(?msg_ccs, ?hmac_cg);
          take_append(ID_SIZE, cs_to_ccs(identifier(0)),
                      append(msg_ccs, ccs_for_cg(hmac_cg)));
          drop_append(ID_SIZE, cs_to_ccs(identifier(0)),
                      append(msg_ccs, ccs_for_cg(hmac_cg)));
          take_append(length(msg_ccs), msg_ccs, ccs_for_cg(hmac_cg));
          drop_append(length(msg_ccs), msg_ccs, ccs_for_cg(hmac_cg));
          public_crypto_chars(buffer_dec, ID_SIZE);
          MEMCMP_SEC(buffer_dec + enc_size - 64, hmac_cg)
        }
    @*/
    //@ chars_to_crypto_chars(buffer_dec, ID_SIZE);
    //@ assert crypto_chars(normal, buffer_dec, ID_SIZE, _);
    //@ close check_identifier_ghost_args(true, garbage, receiver, sender, enc_id, rest_ccs);
    check_identifier(buffer_dec, 0);
    //@ assert id_ccs == cs_to_ccs(identifier(0));

    //Verify the hmac
    sha512_hmac(hmac_key, KEY_SIZE, buffer_dec + ID_SIZE,
                (unsigned int) (enc_size - ID_SIZE - 64), hmac, 0);
    //@ open cryptogram(hmac, 64, ?hmac_ccs2, ?hmac_cg);
    //@ MEMCMP_SEC(hmac, hmac_cg)
    if (memcmp(hmac, (void*) buffer_dec + enc_size - 64, 64) != 0) abort();
    //@ assert hmac_ccs == hmac_ccs2;
    //@ chars_to_secret_crypto_chars(msg, enc_size - ID_SIZE - 64);
    memcpy(msg, buffer_dec + ID_SIZE, (unsigned int) enc_size - ID_SIZE - 64);

    /*@ if (!col && !bad(sender) && !bad(receiver))
        {
          assert [_]hmac_then_enc_tagged_pub_1(?msg_ccs, ?hmac_cg2);
          assert length(pay_ccs) == length(msg_ccs);
          drop_append(ID_SIZE, cs_to_ccs(identifier(0)), 
                      append(pay_ccs, ccs_for_cg(hmac_cg)));
          take_append(ID_SIZE, cs_to_ccs(identifier(0)), 
                      append(pay_ccs, ccs_for_cg(hmac_cg)));
          drop_append(length(pay_ccs), pay_ccs, ccs_for_cg(hmac_cg));
          assert (ccs_for_cg(hmac_cg) == ccs_for_cg(hmac_cg2));
          ccs_for_cg_inj(hmac_cg, hmac_cg2);
          assert pay_ccs == msg_ccs;
        }
    @*/
    //@ chars_join(buffer);
    free(buffer);
    zeroize(hmac, 64);
    zeroize(buffer_dec, ID_SIZE);
    zeroize(buffer_dec + ID_SIZE, enc_size - ID_SIZE - 64);
    zeroize(buffer_dec + enc_size - 64, 64);
    //@ chars_join(buffer_dec);
    free(buffer_dec);
  }
  net_close(socket2);
  net_close(socket1);
  return enc_size - ID_SIZE - 64;
  //@ close principal(receiver, _);
}
