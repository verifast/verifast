#include "yahalom.h"

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

//@ #include "quantifiers.gh"

#define SENDER_PORT 121212
#define RECVER_PORT 232323
#define SERVER_PORT 343434

void auth_enc(havege_state *state, char *key, char *msg,
              unsigned int msg_len, char* output)
/*@ requires [_]public_invar(yahalom_pub) &*&
             havege_state_initialized(state) &*&
             principal(?principal1, _) &*&
             [?f1]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
               key_cg == cg_symmetric_key(?principal2, ?id) &*&
             [?f2]crypto_chars(msg, msg_len, ?msg_cs) &*&
               1024 >= msg_len &*& msg_len >= MIN_ENC_SIZE &*&
             chars(output, 16 + msg_len, _); @*/
/*@ ensures  havege_state_initialized(state) &*&
             principal(principal1, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_cs, key_cg) &*&
             [f2]crypto_chars(msg, msg_len, msg_cs) &*&
             chars(output, 16, ?iv_cs) &*&
             cryptogram(output + 16, msg_len, _, ?enc_cg) &*&
             enc_cg == cg_encrypted(principal2, id, msg_cs, iv_cs); @*/
{
  char iv[16];
  aes_context aes_context;
  unsigned int iv_off = 0;
  //@ chars_limits(output);

  //@ close random_request(principal1, IP(0, 0), false);
  if (havege_random(state, iv, 16) != 0) abort();
  //@ open cryptogram(iv, 16, ?iv_cs, ?iv_cg);
  //@ close yahalom_pub(iv_cg);
  //@ leak yahalom_pub(iv_cg);
  //@ close optional_crypto_chars(!collision_in_run, iv, 16, iv_cs);
  memcpy(output, iv, 16);
  //@ open optional_crypto_chars(!collision_in_run, iv, 16, iv_cs);
  //@ close cryptogram(output, 16, iv_cs, iv_cg);
  //@ public_cryptogram(output, iv_cg);

  //@ close aes_context(&aes_context);
  if (aes_setkey_enc(&aes_context, key, (unsigned int) KEY_SIZE * 8) != 0)
    abort();
  //@ close [f2]optional_crypto_chars(true, msg, msg_len, msg_cs);
  //@ close cryptogram(iv, 16, iv_cs, iv_cg);
  {
    //@ close yahalom_proof_pred();
    //@ PRODUCE_IS_DECRYPTION_ALLOWED(yahalom)
    if (aes_crypt_cfb128(&aes_context, AES_ENCRYPT,
                         (unsigned int) msg_len,
                         &iv_off, iv, msg, output + 16) != 0)
      abort();
    //@ open yahalom_proof_pred();
    //@ leak is_decryption_allowed(_, _, _);
  }
  aes_free(&aes_context);
  //@ open aes_context(&aes_context);
  //@ public_cryptogram(iv, iv_cg);
  
  //@ open [f2]optional_crypto_chars(true, msg, msg_len, msg_cs);
  //@ assert cryptogram(output + 16, msg_len, ?enc_cs, ?enc_cg);
  //@ assert enc_cg == cg_encrypted(principal2, id, msg_cs, iv_cs);
}

void auth_dec(char *key, char *msg, unsigned int msg_len, char* output)
/*@ requires [_]public_invar(yahalom_pub) &*&
             principal(?principal1, _) &*&
             [?f1]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
               key_cg == cg_symmetric_key(?principal2, ?id) &*&
             [?f2]chars(msg, 16, ?iv_cs) &*&
             [f2]chars(msg + 16, msg_len, ?msg_cs) &*&
               msg_len > MIN_ENC_SIZE &*& msg_len < 1024 &*&
             chars(output, msg_len, _); @*/
/*@ ensures  principal(principal1, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_cs, key_cg) &*&
             [f2]chars(msg, 16 + msg_len, append(iv_cs, msg_cs)) &*&
             optional_crypto_chars(!collision_in_run,
                                   output, msg_len, ?dec_cs) &*&
             collision_in_run ?
               [_]public_generated(yahalom_pub)(dec_cs)
             :
               exists(?enc_cg) &*& [_]yahalom_pub(enc_cg) &*&
               msg_cs == chars_for_cg(enc_cg) &*&
               enc_cg == cg_encrypted(principal2, id, dec_cs, iv_cs); @*/
{
  char iv[16];
  aes_context aes_context;
  unsigned int iv_off = 0;
  //@ chars_limits(msg);

  //@ close [f2]optional_crypto_chars(false, msg, 16, iv_cs);
  memcpy(iv, msg, 16);
  //@ open [f2]optional_crypto_chars(false, msg, 16, iv_cs);
  //@ cryptogram iv_cg = chars_for_cg_sur_random(iv_cs);
  //@ public_chars_extract(msg, iv_cg); 
  //@ if (!collision_in_run) crypto_chars(iv, 16, iv_cs);
  //@ close cryptogram(iv, 16, iv_cs, iv_cg);
    
  //@ close aes_context(&aes_context);
  if (aes_setkey_enc(&aes_context, key, (unsigned int) KEY_SIZE * 8) != 0)
    abort();
  //@ close [f2]optional_crypto_chars(false, msg + 16, msg_len, msg_cs);
  {
    //@ close yahalom_proof_pred();
    //@ PRODUCE_IS_DECRYPTION_ALLOWED(yahalom)
    if (aes_crypt_cfb128(&aes_context, AES_DECRYPT,
                          (unsigned int) msg_len,
                          &iv_off, iv, msg + 16, output) != 0)
      abort();
    //@ open yahalom_proof_pred();
    //@ leak is_decryption_allowed(_, _, _);
  }
  //@ open [f2]optional_crypto_chars(false, msg + 16, msg_len, msg_cs);
  //@ public_cryptogram(iv, iv_cg);
  aes_free(&aes_context);
  //@ open aes_context(&aes_context);

  //@ assert optional_crypto_chars(!collision_in_run, output, msg_len, ?dec_cs);
  //@ cryptogram enc_cg = cg_encrypted(principal2, id, dec_cs, iv_cs);
  //@ close exists(enc_cg);
  //@ assert collision_in_run || msg_cs == chars_for_cg(enc_cg);
  /*@ if (!collision_in_run)
      {
        assert chars_for_cg(enc_cg) == msg_cs;
        public_chars_extract(msg + 16, enc_cg);
      }
      else
      {
        public_chars(output, msg_len, dec_cs);
      }
  @*/
  //@ chars_join(msg);
}

void server(int server, int sender, int receiver,
            char *s_key, char *r_key)
/*@ requires [_]public_invar(yahalom_pub) &*&
             principal(server, _) &*&
             [?f1]cryptogram(s_key, KEY_SIZE, ?s_key_cs, ?s_key_cg) &*&
               s_key_cg == cg_symmetric_key(sender, ?s_id) &*&
               cg_info(s_key_cg) == int_pair(3, server) &*&
             [?f2]cryptogram(r_key, KEY_SIZE, ?r_key_cs, ?r_key_cg) &*&
               r_key_cg == cg_symmetric_key(receiver, ?r_id) &*&
               cg_info(r_key_cg) == int_pair(3, server); @*/
/*@ ensures  [_]public_invar(yahalom_pub) &*&
             principal(server, _) &*&
             [f1]cryptogram(s_key, KEY_SIZE, s_key_cs, s_key_cg) &*&
             [f2]cryptogram(r_key, KEY_SIZE, r_key_cs, r_key_cg); @*/
{
  int socket;
  int socket_in;
  int socket_out;
  havege_state havege_state;
  char NA[NONCE_SIZE];
  //@ cryptogram NB_cg;
  char NB[NONCE_SIZE];
  //@ cryptogram NA_cg;
  char KAB[KEY_SIZE];

  if(net_bind(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_accept(socket, &socket_in, NULL) != 0)
    abort();
  if(net_set_block(socket_in) != 0)
    abort();
  net_usleep(60000);
  if(net_connect(&socket_out, NULL, SENDER_PORT) != 0)
    abort();
  if(net_set_block(socket_out) != 0)
    abort();

  //@ assert integer(&sender, ?sendr_val);
  //@ assert integer(&receiver, ?recvr_val);

  //@ close havege_state(&havege_state);
  havege_init(&havege_state);

  {
    // 2. B -> S. B, ENC(KB, {A, NA, NB})
    int prefix_size = 4 + NONCE_SIZE;
    int d_size = prefix_size + NONCE_SIZE;
    char *decrypted = malloc(d_size); if (decrypted == 0) abort();
    int m_size = 4 + 16 + d_size;
    char *message = malloc(m_size); if (message == 0) abort();

    // Receive the message
    net_recv(&socket_in, message, (unsigned int) m_size);

    //@ assert chars(message, 4, _);
    //@ integer_to_chars(&receiver);
    /*@ close optional_crypto_chars(false, (void*) &receiver,
                                    4, chars_of_int(recvr_val)); @*/
    //@ close optional_crypto_chars(false, message, 4, _);
    if (memcmp(message, (void*) &receiver, 4) != 0) abort();
    //@ open optional_crypto_chars(false, message, 4, _);
    //@ chars_to_integer(&receiver);

    auth_dec(r_key, (void*) message + 4, (unsigned int) d_size, decrypted);
    /*@ open optional_crypto_chars(!collision_in_run,
                                   decrypted, d_size, ?dec_cs); @*/
    //@ cryptogram enc_cg;
    /*@ if (!collision_in_run)
        {
          crypto_chars_split(decrypted, 4);
          crypto_chars_split((void*) decrypted + 4, NONCE_SIZE);
          assert exists(?enc_cg2);
          enc_cg = enc_cg2;
          open [_]yahalom_pub(enc_cg);
        }
    @*/
    //@ integer_to_chars(&sender);
    /*@ close optional_crypto_chars(false, (void*) &sender,
                                    4, chars_of_int(sendr_val)); @*/
    //@ close optional_crypto_chars(!collision_in_run, decrypted, 4, _);
    if (memcmp(decrypted, (void*) &sender, 4) != 0) abort();
    //@ open optional_crypto_chars(!collision_in_run, decrypted, 4, _);
    //@ chars_to_integer(&sender);

    /*@ close optional_crypto_chars(!collision_in_run, (void*) decrypted + 4,
                                    NONCE_SIZE, ?NA_cs); @*/
    memcpy(NA, (void*) decrypted + 4, NONCE_SIZE);
    /*@ open optional_crypto_chars(!collision_in_run, (void*) decrypted + 4,
                                   NONCE_SIZE, NA_cs); @*/
    //@ open optional_crypto_chars(!collision_in_run, NA, NONCE_SIZE, NA_cs);
    /*@ close optional_crypto_chars(!collision_in_run,
                                    (void*) decrypted + 4 + NONCE_SIZE,
                                    NONCE_SIZE, ?NB_cs); @*/
    memcpy(NB, (void*) decrypted + prefix_size, NONCE_SIZE);
    /*@ open optional_crypto_chars(!collision_in_run,
                                   (void*) decrypted + 4 + NONCE_SIZE,
                                   NONCE_SIZE, NB_cs); @*/
    //@ open optional_crypto_chars(!collision_in_run, NB, NONCE_SIZE, NB_cs);
    //@ NA_cg = chars_for_cg_sur_random(NA_cs);
    //@ NB_cg = chars_for_cg_sur_random(NB_cs);
    /*@ if (!collision_in_run)
        {
          crypto_chars_join((void*) decrypted + 4);
          crypto_chars_join(decrypted);

          if (yahalom_public_key(recvr_val, r_id))
          {
            public_crypto_chars(decrypted, d_size, dec_cs);
            chars_split(decrypted, 4);
            chars_split((void*) decrypted + 4, NONCE_SIZE);
            public_chars((void*) decrypted + 4, NONCE_SIZE, NA_cs);
            public_crypto_chars_extract(NA, NA_cg);
            public_chars((void*) decrypted + 4 + NONCE_SIZE, NONCE_SIZE, NB_cs);
            public_crypto_chars_extract(NB, NB_cg);
            chars_join((void*) decrypted + 4);
            chars_join(decrypted);
            crypto_chars(decrypted, d_size, dec_cs);
            public_crypto_chars(NA, NONCE_SIZE, NA_cs);
          }
          else
          {
            assert [_]yahalom_pub_msg1(?srv2, ?s2, ?NA2, ?NB2);
            take_append(4, chars_of_int(sendr_val), append(NA_cs, NB_cs));
            take_append(4, chars_of_int(s2),
                           append(chars_for_cg(NA2), chars_for_cg(NB2)));
            drop_append(4, chars_of_int(sendr_val), append(NA_cs, NB_cs));
            drop_append(4, chars_of_int(s2),
                           append(chars_for_cg(NA2), chars_for_cg(NB2)));
            take_append(NONCE_SIZE, NA_cs, NB_cs);
            take_append(NONCE_SIZE, chars_for_cg(NA2), chars_for_cg(NB2));
            drop_append(NONCE_SIZE, NA_cs, NB_cs);
            drop_append(NONCE_SIZE, chars_for_cg(NA2), chars_for_cg(NB2));
            assert srv2 == server;
            chars_of_int_injective(s2, sender);
            assert s2 == sender;
            assert chars_for_cg(NA2) == NA_cs;
            NA_cg = NA2;
            close cryptogram(NA, NONCE_SIZE, NA_cs, NA_cg);
            public_cryptogram(NA, NA_cg);
            assert chars_for_cg(NB2) == NB_cs;
            NB_cg = NB2;
            assert NB_cg == cg_random(recvr_val, _);
          }
        }
        else
        {
          chars_join(decrypted);
        }
    @*/

    //@ close optional_crypto_chars(!collision_in_run, decrypted, d_size, _);
    zeroize(decrypted, d_size);
    free(decrypted);
    //@ chars_join(message);
    free(message);
  }

  //@ assert chars(NA, NONCE_SIZE, ?cs_NA);
  //@ public_chars(NA, NONCE_SIZE, cs_NA);
  //@ assert collision_in_run || cs_NA == chars_for_cg(NA_cg);
  //@ assert NA_cg == cg_random(?s2, ?a_id);
  //@ assert optional_crypto_chars(!collision_in_run, NB, NONCE_SIZE, ?cs_NB);
  //@ assert collision_in_run || cs_NB == chars_for_cg(NB_cg);
  //@ assert NB_cg == cg_random(?r2, ?b_id);

  /*@ close random_request(server, IP(4, IP(sender, IP(receiver,
                                   IP(s2, IP(a_id, IP(r2, b_id)))))), true); @*/
  if (havege_random(&havege_state, KAB, KEY_SIZE) != 0) abort();
  //@ open cryptogram(KAB, KEY_SIZE, ?cs_KAB, ?cg_KAB);
  //@ assert cg_KAB == cg_symmetric_key(server, ?id_KAB);
  /*@ if (yahalom_public_key(server, id_KAB))
      {
        close cryptogram(KAB, KEY_SIZE, cs_KAB, cg_KAB);
        close yahalom_pub(cg_KAB);
        leak yahalom_pub(cg_KAB);
        public_cryptogram(KAB, cg_KAB);
        public_chars(KAB, KEY_SIZE, cs_KAB);
        assert [_]public_generated(yahalom_pub)(cs_KAB);
        if (!collision_in_run)
          crypto_chars(KAB, KEY_SIZE, cs_KAB);
      }
  @*/

  {
    // 3. S -> A. ENC(KA, {B, KAB, NA, NB}), ENC(KB, {A, KAB})
    int size1 = 16 + 4 + KEY_SIZE + NONCE_SIZE + NONCE_SIZE;
    int size2 = 16 + 4 + KEY_SIZE;
    char *enc1 = malloc(size1); if (enc1 == 0) abort();
    char *enc2 = malloc(size2); if (enc2 == 0) abort();
    {
      //ENC(KA, {B, KAB, NA, NB})
      int s = 4 + KEY_SIZE + NONCE_SIZE + NONCE_SIZE;
      char* m = malloc(s); if (m == 0) abort();
      //@ integer_to_chars(&receiver);
      /*@ close optional_crypto_chars(false, (void*) &receiver,
                                      4, chars_of_int(recvr_val)); @*/
      memcpy(m, &receiver, 4);
      /*@ open optional_crypto_chars(false, (void*) &receiver,
                                      4, chars_of_int(recvr_val)); @*/
      //@ chars_to_integer(&receiver);
      //@ public_chars(m, 4, chars_of_int(recvr_val));
      //@ crypto_chars(m, 4, chars_of_int(recvr_val));
      //@ close optional_crypto_chars(!collision_in_run, KAB, KEY_SIZE, cs_KAB);
      memcpy(m + 4, KAB, KEY_SIZE);
      //@ open optional_crypto_chars(!collision_in_run, KAB, KEY_SIZE, cs_KAB);
      //@ open optional_crypto_chars(!collision_in_run, m + 4, KEY_SIZE,cs_KAB);
      //@ close optional_crypto_chars(false, NA, NONCE_SIZE, cs_NA);
      memcpy(m + 4 + KEY_SIZE, NA, NONCE_SIZE);
      //@ crypto_chars(m + 4 + KEY_SIZE, NONCE_SIZE, cs_NA);
      //@ close optional_crypto_chars(!collision_in_run, NB, NONCE_SIZE, cs_NB);
      memcpy(m + 4 + KEY_SIZE + NONCE_SIZE, NB, NONCE_SIZE);
      /*@ open optional_crypto_chars(!collision_in_run,
                                     m + 4 + KEY_SIZE + NONCE_SIZE,
                                     NONCE_SIZE, cs_NB); @*/
      /*@ if (collision_in_run)
          {
            public_chars(KAB, KEY_SIZE, cs_KAB);
            crypto_chars(m + 4, KEY_SIZE, cs_KAB);
            public_chars(NB, NONCE_SIZE, cs_NB);
            crypto_chars(m + 4 + KEY_SIZE + NONCE_SIZE, NONCE_SIZE, cs_NB);
          }
      @*/
      //@ crypto_chars_join(m + 4 + KEY_SIZE);
      //@ crypto_chars_join(m + 4);
      //@ crypto_chars_join(m);

      auth_enc(&havege_state, s_key, m,
               (unsigned int) (4 + KEY_SIZE + NONCE_SIZE + NONCE_SIZE), enc1);
      /*@ open cryptogram(enc1 + 16, 4 + KEY_SIZE + NONCE_SIZE + NONCE_SIZE,
                          ?enc_cs, ?enc_cg); @*/
      /*@ if (!collision_in_run)
          {
            list <char> dec_cs = append(chars_of_int(recvr_val),
                                 append(cs_KAB, append(cs_NA, cs_NB)));
            assert enc_cg == cg_encrypted(sendr_val, s_id, dec_cs, ?ent);

            if (yahalom_public_key(sendr_val, s_id))
            {
              assert true == yahalom_public_key(server, id_KAB);
              take_append(4, chars_of_int(recvr_val),
                          append(cs_KAB, append(cs_NA, cs_NB)));
              drop_append(4, chars_of_int(recvr_val),
                          append(cs_KAB, append(cs_NA, cs_NB)));
              take_append(KEY_SIZE, cs_KAB, append(cs_NA, cs_NB));
              drop_append(KEY_SIZE, cs_KAB, append(cs_NA, cs_NB));
              take_append(NONCE_SIZE, cs_NA, cs_NB);
              crypto_chars_split(m, 4);
              crypto_chars_split(m + 4, KEY_SIZE);
              crypto_chars_split(m + 4 + KEY_SIZE, NONCE_SIZE);
              public_crypto_chars(m, 4, chars_of_int(recvr_val));
              close yahalom_pub(cg_KAB);
              leak yahalom_pub(cg_KAB);
              close cryptogram(m + 4, KEY_SIZE, cs_KAB, cg_KAB);
              public_cryptogram(m + 4, cg_KAB);
              public_crypto_chars(m + 4 + KEY_SIZE, NONCE_SIZE, cs_NA);
              if (yahalom_public_key(recvr_val, r_id))
              {
                public_crypto_chars(m + 4 + KEY_SIZE + NONCE_SIZE,
                                    NONCE_SIZE, cs_NB);
              }
              else
              {
                close yahalom_pub(NB_cg);
                leak yahalom_pub(NB_cg);
                close cryptogram(m + 4 + KEY_SIZE + NONCE_SIZE,
                                 NONCE_SIZE, cs_NB, NB_cg);
                public_cryptogram(m + 4 + KEY_SIZE + NONCE_SIZE, NB_cg);
              }
              chars_join(m + 4 + KEY_SIZE);
              chars_join(m + 4);
              chars_join(m);
              public_chars(m, s, dec_cs);
              crypto_chars(m, s, dec_cs);
            }
            else
            {
              close yahalom_pub_msg2(server, receiver, NA_cg, NB_cg, cg_KAB);
            }
            close yahalom_pub(enc_cg);
            leak yahalom_pub(enc_cg);
            close cryptogram(enc1 + 16, 4 + KEY_SIZE + NONCE_SIZE + NONCE_SIZE,
                             enc_cs, enc_cg);
            public_cryptogram(enc1 + 16, enc_cg);
          }
      @*/

      /*@ close optional_crypto_chars(true, m,
                                 4 + KEY_SIZE + NONCE_SIZE + NONCE_SIZE, _); @*/
      zeroize(m, 4 + KEY_SIZE + NONCE_SIZE + NONCE_SIZE);
      free(m);
    }

    {
      //ENC(KB, {A, KAB})
      int s = 4 + KEY_SIZE;
      char* m = malloc(s); if (m == 0) abort();
      //@ integer_to_chars(&sender);
      /*@ close optional_crypto_chars(false, (void*) &sender,
                                      4, chars_of_int(sendr_val)); @*/
      memcpy(m, &sender, 4);
      /*@ open optional_crypto_chars(false, (void*) &sender,
                                      4, chars_of_int(sendr_val)); @*/
      //@ chars_to_integer(&sender);
      //@ public_chars(m, 4, chars_of_int(sendr_val));
      //@ crypto_chars(m, 4, chars_of_int(sendr_val));
      //@ close optional_crypto_chars(!collision_in_run, KAB, KEY_SIZE, cs_KAB);
      memcpy(m + 4, KAB, KEY_SIZE);
      //@ open optional_crypto_chars(!collision_in_run, KAB, KEY_SIZE, cs_KAB);
      //@ open optional_crypto_chars(!collision_in_run, m + 4, KEY_SIZE,cs_KAB);
      /*@ if (collision_in_run)
          {
            public_chars(KAB, KEY_SIZE, cs_KAB);
            crypto_chars(m + 4, KEY_SIZE, cs_KAB);
          }
      @*/
      //@ crypto_chars_join(m);

      auth_enc(&havege_state, r_key, m, (unsigned int) (4 + KEY_SIZE), enc2);
      //@ open cryptogram(enc2 + 16, 4 + KEY_SIZE, ?enc_cs, ?enc_cg);
      /*@ if (!collision_in_run)
          {
            assert enc_cg == cg_encrypted(recvr_val, r_id,
                                append(chars_of_int(sendr_val), cs_KAB), ?ent);
            if (yahalom_public_key(recvr_val, r_id))
            {
              assert true == yahalom_public_key(server, id_KAB);
              take_append(4, chars_of_int(sendr_val), cs_KAB);
              drop_append(4, chars_of_int(sendr_val), cs_KAB);
              crypto_chars_split(m, 4);
              public_crypto_chars(m, 4, chars_of_int(sendr_val));
              close cryptogram(m + 4, KEY_SIZE, cs_KAB, cg_KAB);
              close yahalom_pub(cg_KAB);
              leak yahalom_pub(cg_KAB);
              public_cryptogram(m + 4, cg_KAB);
              chars_join(m);
              public_chars(m, s, append(chars_of_int(sendr_val), cs_KAB));
              crypto_chars(m, s, append(chars_of_int(sendr_val), cs_KAB));
            }
            else
            {
              close yahalom_pub_msg3(server, sender, cg_KAB,
                                     s2, a_id, r2, b_id);
            }
            close yahalom_pub(enc_cg);
            leak yahalom_pub(enc_cg);
            close cryptogram(enc2 + 16, 4 + KEY_SIZE, enc_cs, enc_cg);
            public_cryptogram(enc2 + 16, enc_cg);
          }
      @*/

      //@ close optional_crypto_chars(true, m, 4 + KEY_SIZE, _);
      zeroize(m, 4 + KEY_SIZE);
      free(m);
    }

    {
      int size = size1 + size2;
      char *message = malloc(size); if (message == 0) abort();
      //@ close optional_crypto_chars(false, enc1, size1, _);
      memcpy(message, enc1, (unsigned int) size1);
      //@ open optional_crypto_chars(false, message, size1, _);
      //@ close optional_crypto_chars(false, enc2, size2, _);
      memcpy(message + size1, enc2, (unsigned int) size2);
      //@ open optional_crypto_chars(false, message + size1, size2, _);
      //@ chars_join(message);
      net_send(&socket_out, message, (unsigned int) size);
      free(message);
    }

    free(enc1);
    free(enc2);
  }

  havege_free(&havege_state);
  //@ open havege_state(&havege_state);

  /*@ close optional_crypto_chars(!collision_in_run, KAB, KEY_SIZE, _); @*/
  zeroize(KAB, KEY_SIZE);
  //@ close optional_crypto_chars(!collision_in_run, NB, NONCE_SIZE, _);
  zeroize(NB, NONCE_SIZE);

  net_close(socket);
  net_close(socket_in);
  net_close(socket_out);
}

void sender(int server, int sender, int receiver,
            char *key, char *generated_key)
/*@ requires [_]public_invar(yahalom_pub) &*&
             principal(sender, ?s_id1) &*&
             [?f]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
               key_cg == cg_symmetric_key(sender, ?s_id2) &*&
               cg_info(key_cg) == int_pair(3, server) &*&
             chars(generated_key, KEY_SIZE, _); @*/
/*@ ensures  [_]public_invar(yahalom_pub) &*&
             principal(sender, _) &*&
             [f]cryptogram(key, KEY_SIZE, key_cs, key_cg) &*&
             cryptogram(generated_key, KEY_SIZE, _, ?g_key_cg) &*&
             collision_in_run || bad(server) || bad(sender) ?
               true
             :
               g_key_cg == cg_symmetric_key(server, ?id) &*&
               IF(cg_info(g_key_cg)) == 4 &*&
               IF(IS(cg_info(g_key_cg))) == sender &*&
               IF(IS(IS(cg_info(g_key_cg)))) == receiver &*&
               IF(IS(IS(IS(cg_info(g_key_cg))))) == sender &*&
               IF(IS(IS(IS(IS(cg_info(g_key_cg)))))) ==  s_id1 + 1 &*&
               bad(receiver) ||
                 IF(IS(IS(IS(IS(IS(cg_info(g_key_cg))))))) == receiver &&
                 !yahalom_public_key(server, id); @*/
{
  int socket;
  int socket_in;
  int socket_out;
  havege_state havege_state;
  char NA[NONCE_SIZE];
  char NB[NONCE_SIZE];
  char *MB;
  //@ cryptogram cg_NB;
  //@ cryptogram cg_KAB;

  net_usleep(40000);
  if(net_connect(&socket_out, NULL, RECVER_PORT) != 0)
    abort();
  if(net_set_block(socket_out) != 0)
    abort();
  if(net_bind(&socket, NULL, SENDER_PORT) != 0)
    abort();
  if(net_accept(socket, &socket_in, NULL) != 0)
    abort();
  if(net_set_block(socket_in) != 0)
    abort();

  //@ assert integer(&sender, ?sendr_val);
  //@ assert integer(&receiver, ?recvr_val);

  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  /*@ close random_request(sender, int_pair(1,
                                     int_pair(sender, receiver)), false); @*/
  if (havege_random(&havege_state, NA, NONCE_SIZE) != 0) abort();
  //@ assert cryptogram(NA, NONCE_SIZE, ?cs_NA, ?cg_NA);
  //@ assert cg_NA == cg_random(sendr_val, s_id1 + 1);
  //@ close yahalom_pub(cg_NA);
  //@ leak yahalom_pub(cg_NA);
  //@ public_cryptogram(NA, cg_NA);

  {
    // 1. A -> B. A, NA
    char* message = malloc(4 + NONCE_SIZE); if (message == 0) abort();

    //@ integer_to_chars(&sender);
    /*@ close optional_crypto_chars(false, (void*) &sender,
                                    4, chars_of_int(sendr_val)); @*/
    memcpy(message, &sender, 4);
    /*@ open optional_crypto_chars(false, (void*) &sender,
                                    4, chars_of_int(sendr_val)); @*/
    //@ open optional_crypto_chars(false, message, 4, chars_of_int(sendr_val));
    //@ chars_to_integer(&sender);
    //@ close optional_crypto_chars(false, NA, NONCE_SIZE, cs_NA);
    memcpy((void*) message + 4, NA, NONCE_SIZE);
    //@ open optional_crypto_chars(false, NA, NONCE_SIZE, cs_NA);
    /*@ open optional_crypto_chars(false, (void*) message + 4,
                                   NONCE_SIZE, cs_NA); @*/

    net_send(&socket_out, message, (unsigned int) 4 + NONCE_SIZE);
    free(message);
  }

  {
    // 3. S -> A. ENC(KA, {B, KAB, NA, NB}), ENC(KB, {A, KAB})
    int size1 = 4 + KEY_SIZE + NONCE_SIZE + NONCE_SIZE;
    int size2 = 16 + 4 + KEY_SIZE;
    int size = 16 + size1 + size2;
    char *msg = malloc(size); if (msg == 0) abort();
    char *dec = malloc(size1); if (dec == 0) abort();
    MB = malloc(size2); if (MB == 0) abort();

    net_recv(&socket_in, msg, (unsigned int) size);
    auth_dec(key, (void*) msg, (unsigned int) size1, dec);
    //@ close optional_crypto_chars(false, msg + 16 + size1, size2, ?cs_msg2);
    memcpy(MB, msg + 16 + size1, (unsigned int) size2);
    //@ open optional_crypto_chars(false, msg + 16 + size1, size2, cs_msg2);

    //@ open optional_crypto_chars(!collision_in_run, dec, size1, ?dec_cs);
    //@ cryptogram enc_cg;
    /*@ if (!collision_in_run)
        {
          crypto_chars_split(dec, 4);
          crypto_chars_split(dec + 4, KEY_SIZE);
          crypto_chars_split(dec + 4 + KEY_SIZE, NONCE_SIZE);
          assert exists(?enc_cg2);
          enc_cg = enc_cg2;
          open [_]yahalom_pub(enc_cg);
        }
    @*/
    //@ integer_to_chars(&receiver);
    /*@ close optional_crypto_chars(false, (void*) &receiver,
                                    4, chars_of_int(recvr_val)); @*/
    //@ close optional_crypto_chars(!collision_in_run, dec, 4, _);
    if (memcmp(dec, (void*) &receiver, 4) != 0) abort();
    //@ open optional_crypto_chars(!collision_in_run, dec, 4, _);
    //@ chars_to_integer(&receiver);

    /*@ close optional_crypto_chars(!collision_in_run,
                                    (void*) dec + 4, KEY_SIZE, ?cs_KAB); @*/
    memcpy(generated_key, (void*) dec + 4, KEY_SIZE);
    /*@ open optional_crypto_chars(!collision_in_run,
                                   (void*) dec + 4, KEY_SIZE, cs_KAB); @*/
    //@ close optional_crypto_chars(false, NA, NONCE_SIZE, cs_NA);
    /*@ close optional_crypto_chars(!collision_in_run,
                                    dec + 4 + KEY_SIZE, NONCE_SIZE, _); @*/
    if (memcmp(NA, dec + 4 + KEY_SIZE, NONCE_SIZE) != 0) abort();
    /*@ open optional_crypto_chars(!collision_in_run, dec + 4 + KEY_SIZE,
                                   NONCE_SIZE, cs_NA); @*/
    /*@ close optional_crypto_chars(!collision_in_run,
                                    (void*) dec + 4 + KEY_SIZE + NONCE_SIZE,
                                    NONCE_SIZE, ?cs_NB); @*/
    memcpy(NB, (void*) dec + 4 + KEY_SIZE + NONCE_SIZE, NONCE_SIZE);
    /*@ open optional_crypto_chars(!collision_in_run,
                                   (void*) dec + 4 + KEY_SIZE + NONCE_SIZE,
                                   NONCE_SIZE, cs_NB); @*/
    //@ cg_NB = chars_for_cg_sur_random(cs_NB);
    /*@ assert dec_cs == append(chars_of_int(recvr_val),
                           append(cs_KAB, append(cs_NA, cs_NB))); @*/
    free(msg);
    /*@ if (collision_in_run)
        {
          chars_join(dec + 4 + KEY_SIZE);
          chars_join(dec + 4);
          chars_join(dec);
        }
        else
        {
          crypto_chars_join(dec + 4 + KEY_SIZE);
          crypto_chars_join(dec + 4);
          crypto_chars_join(dec);
        }
    @*/
    //@ cg_KAB = chars_for_cg_sur_symmetric_key(cs_KAB);
    /*@ if (collision_in_run || yahalom_public_key(sender, s_id2))
        {
          assert [_]public_generated(yahalom_pub)(dec_cs);
          if (!collision_in_run)
          {
            public_crypto_chars(dec, size1, dec_cs);
            chars_split(dec, 4);
            chars_split(dec + 4, KEY_SIZE);
            chars_split(dec + 4 + KEY_SIZE, NONCE_SIZE);
            public_chars_extract(dec + 4, cg_KAB);
            public_chars(dec + 4 + KEY_SIZE + NONCE_SIZE, NONCE_SIZE, cs_NB);
            chars_join(dec + 4 + KEY_SIZE);
            chars_join(dec + 4);
            chars_join(dec);
            crypto_chars(dec, size1, dec_cs);
          }
        }
        else
        {
          assert [_]yahalom_pub_msg2(?server2, ?receiver2, ?NA2, ?NB2, ?KAB2);
          assert length(chars_of_int(receiver2)) == 4;
          take_append(4, chars_of_int(receiver2), append(chars_for_cg(KAB2),
                      append(chars_for_cg(NA2), chars_for_cg(NB2))));
          drop_append(4, chars_of_int(receiver2), append(chars_for_cg(KAB2),
                      append(chars_for_cg(NA2), chars_for_cg(NB2))));
          take_append(4, chars_of_int(recvr_val), append(cs_KAB,
                      append(cs_NA, cs_NB)));
          drop_append(4, chars_of_int(recvr_val), append(cs_KAB,
                      append(cs_NA, cs_NB)));
          take_append(KEY_SIZE, chars_for_cg(KAB2),
                      append(chars_for_cg(NA2), chars_for_cg(NB2)));
          drop_append(KEY_SIZE, chars_for_cg(KAB2),
                      append(chars_for_cg(NA2), chars_for_cg(NB2)));
          take_append(KEY_SIZE, cs_KAB, append(cs_NA, cs_NB));
          drop_append(KEY_SIZE, cs_KAB, append(cs_NA, cs_NB));
          take_append(NONCE_SIZE, chars_for_cg(NA2), chars_for_cg(NB2));
          drop_append(NONCE_SIZE, chars_for_cg(NA2), chars_for_cg(NB2));
          take_append(NONCE_SIZE, cs_NA, cs_NB);
          drop_append(NONCE_SIZE, cs_NA, cs_NB);
          chars_of_int_injective(receiver2, receiver);
          assert receiver2 == recvr_val;
          cg_KAB = KAB2;
          assert cg_KAB == cg_symmetric_key(server, _);
          chars_for_cg_inj_random(cg_NA, NA2);
          assert cg_NA == cg_random(?s, ?a_id);
          assert NB2 == cg_random(?r, ?b_id);
          cg_NB = NB2;
          chars_for_cg_inj_random(cg_NB, NB2);
          assert chars_for_cg(cg_NB) == cs_NB;
          assert server2 == server;
          assert cg_info(cg_KAB) == IP(4, IP(sender, IP(receiver,
                                      IP(s, IP(a_id, IP(r, b_id))))));
        }
    @*/
    //@ close cryptogram(generated_key, KEY_SIZE, cs_KAB, cg_KAB);
    //@ close optional_crypto_chars(!collision_in_run, dec, size1, _);
    zeroize(dec, size1);
    free(dec);
  }

  //@ assert optional_crypto_chars(!collision_in_run, NB, NONCE_SIZE, ?cs_NB);
  //@ assert collision_in_run || cs_NB == chars_for_cg(cg_NB);
  //@ assert cryptogram(generated_key, KEY_SIZE, ?cs_KAB, cg_KAB);
  //@ assert cg_KAB == cg_symmetric_key(?p0, ?c0);
  //@ assert collision_in_run || bad(sender) || bad(server) || p0 == server;
  {
    // 4. A -> B. ENC(KB, {A, KAB}), ENC(KAB, NB)
    int size1 = 16 + 4 + KEY_SIZE;
    int size2 = 16 + NONCE_SIZE;
    char *enc2 = malloc(size2); if (enc2 == 0) abort();
    {
      /*@ if (collision_in_run)
          {
            public_chars(NB, NONCE_SIZE, cs_NB);
            crypto_chars(NB, NONCE_SIZE, cs_NB);
          }
      @*/
      auth_enc(&havege_state, generated_key, NB, NONCE_SIZE, enc2);
      //@ if (collision_in_run) public_crypto_chars(NB, NONCE_SIZE, cs_NB);
      //@ open cryptogram(enc2 + 16, NONCE_SIZE, ?enc_cs, ?enc_cg);
      //@ assert cg_NA == cg_random(?sender2, ?a_id);
      //@ assert cg_NB == cg_random(?receiver2, ?b_id);
      /*@ if (!collision_in_run)
          {
            if (yahalom_public_key(p0, c0))
            {
              if (!bad(sender) && !bad(server) && bad(receiver))
              {
                assert [_]yahalom_pub(cg_NB);
                close cryptogram(NB, NONCE_SIZE, cs_NB, cg_NB);
                public_cryptogram(NB, cg_NB);
                public_chars(NB, NONCE_SIZE, cs_NB);
                crypto_chars(NB, NONCE_SIZE, cs_NB);
              }
            }
            else
            {
              if (bad(server) || bad(sender) || bad(server))
              {
                public_crypto_chars_extract(NB, cg_NB);
              }
              close yahalom_pub_msg4(server, sender, receiver, a_id, cg_NB);
            }
            close yahalom_pub(enc_cg);
            leak yahalom_pub(enc_cg);
            close cryptogram(enc2 + 16, NONCE_SIZE, enc_cs, enc_cg);
            public_cryptogram(enc2 + 16, enc_cg);
          }
      @*/
      //@ chars_join(enc2);
    }

    {
      int size = size1 + size2;
      char *message = malloc(size); if (message == 0) abort();
      //@ close optional_crypto_chars(false, MB, size1, _);
      memcpy(message, MB, (unsigned int) size1);
      //@ open optional_crypto_chars(false, message, size1, _);
      //@ close optional_crypto_chars(false, enc2, size2, _);
      memcpy(message + size1, enc2, (unsigned int) size2);
      //@ open optional_crypto_chars(false, message + size1, size2, _);
      //@ chars_join(message);
      net_send(&socket_out, message, (unsigned int) size);
      free(message);
    }

    free(enc2);
  }

  //@ close optional_crypto_chars(!collision_in_run, NB, NONCE_SIZE, _);
  zeroize(NB, NONCE_SIZE);
  free(MB);

  havege_free(&havege_state);
  //@ open havege_state(&havege_state);

  net_close(socket);
  net_close(socket_in);
  net_close(socket_out);
}

void receiver(int server, int sender, int receiver,
              char *key, char *generated_key)
/*@ requires [_]public_invar(yahalom_pub) &*&
             principal(receiver, ?r_id1) &*&
             [?f]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
               key_cg == cg_symmetric_key(receiver, ?r_id2) &*&
               cg_info(key_cg) == int_pair(3, server) &*&
             chars(generated_key, KEY_SIZE, _); @*/
/*@ ensures  [_]public_invar(yahalom_pub) &*&
             principal(receiver, _) &*&
             [f]cryptogram(key, KEY_SIZE, key_cs, key_cg) &*&
             cryptogram(generated_key, KEY_SIZE, _, ?g_key_cg) &*&
             collision_in_run || bad(server) || bad(sender) || bad(receiver) ?
               true
             :
               g_key_cg == cg_symmetric_key(server, ?id) &*&
               IF(cg_info(g_key_cg)) == 4 &*&
               IF(IS(cg_info(g_key_cg))) == sender &*&
               IF(IS(IS(cg_info(g_key_cg)))) == receiver &*&
               IF(IS(IS(IS(cg_info(g_key_cg))))) == sender &*&
               IF(IS(IS(IS(IS(IS(cg_info(g_key_cg))))))) == receiver &*&
               IS(IS(IS(IS(IS(IS(cg_info(g_key_cg))))))) == r_id1 + 1; @*/
{
  int socket;
  int socket_in;
  int socket_out;
  havege_state havege_state;
  char NA[NONCE_SIZE];
  char NB[NONCE_SIZE];
  //@ cryptogram cg_KAB;

  net_usleep(20000);
  if(net_connect(&socket_out, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket_out) != 0)
    abort();
  if(net_bind(&socket, NULL, RECVER_PORT) != 0)
    abort();
  if(net_accept(socket, &socket_in, NULL) != 0)
    abort();
  if(net_set_block(socket_in) != 0)
    abort();

  //@ assert integer(&sender, ?sendr_val);
  //@ assert integer(&receiver, ?recvr_val);

  {
    // 1. A -> B. A, NA
    int size = 4 + NONCE_SIZE;
    char* message = malloc(size); if (message == 0) abort();
    net_recv(&socket_in, message, (unsigned int) size);
    //@ assert chars(message, 4, _);
    //@ integer_to_chars(&sender);
    /*@ close optional_crypto_chars(false, (void*) &sender,
                                    4, chars_of_int(sendr_val)); @*/
    //@ close optional_crypto_chars(false, message, 4, _);
    if (memcmp(message, (void*) &sender, 4) != 0 ) abort();
    //@ open optional_crypto_chars(false, message, 4, _);
    //@ chars_to_integer(&sender);
    //@ assert chars(message, 4, _);
    /*@ close optional_crypto_chars(false, (void*) message + 4,
                                    NONCE_SIZE, ?cs_NA); @*/
    memcpy(NA, (void*) message + 4, NONCE_SIZE);
    /*@ open optional_crypto_chars(false, (void*) message + 4,
                                   NONCE_SIZE, cs_NA); @*/
    //@ public_chars((void*) message + 4, NONCE_SIZE, cs_NA);

    free(message);
  }

  //@ open optional_crypto_chars(false, NA, NONCE_SIZE, ?cs_NA);
  //@ cryptogram cg_NA = chars_for_cg_sur_random(cs_NA);
  //@ assert cg_NA == cg_random(?s, ?s_id);
  //@ public_chars_extract(NA, cg_NA);
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  /*@ close random_request(recvr_val, IP(2, IP(server,
                                       IP(sender, IP(s, s_id)))), false); @*/
  if (havege_random(&havege_state, NB, NONCE_SIZE) != 0) abort();
  //@ open cryptogram(NB, NONCE_SIZE, ?cs_NB, ?cg_NB);

  /*@ if (bad(server) || bad(sender) || bad(receiver))
      {
        close cryptogram(NB, NONCE_SIZE, cs_NB, cg_NB);
        close yahalom_pub(cg_NB);
        leak yahalom_pub(cg_NB);
        public_cryptogram(NB, cg_NB);
        public_chars(NB, NONCE_SIZE, cs_NB);
        assert [_]public_generated(yahalom_pub)(cs_NB);
        if (!collision_in_run) crypto_chars(NB, NONCE_SIZE, cs_NB);
      }
  @*/

  {
    // 2. B -> S. B, ENC(KB, {A, NA, NB})
    int prefix_size = 4 + NONCE_SIZE;
    int p_size = prefix_size + NONCE_SIZE;
    char *plaintext = malloc(p_size); if (plaintext == 0) abort();
    int m_size = 4 + 16 + p_size;
    char *message = malloc(m_size); if (message == 0) abort();
    //@ assert chars(message, 4, _);
    //@ integer_to_chars(&receiver);
    /*@ close optional_crypto_chars(false, (void*) &receiver,
                                    4, chars_of_int(recvr_val)); @*/
    //@ close optional_crypto_chars(false, message, 4, _);
    memcpy(message, (void*) &receiver, 4);
    //@ open optional_crypto_chars(false, message, 4, _);
    //@ chars_to_integer(&receiver);

    //@ assert chars(plaintext, 4, _);
    //@ integer_to_chars(&sender);
    /*@ close optional_crypto_chars(false, (void*) &sender,
                                    4, chars_of_int(sendr_val)); @*/
    //@ close optional_crypto_chars(false, plaintext, 4, _);
    memcpy(plaintext, (void*) &sender, 4);
    //@ open optional_crypto_chars(false, plaintext, 4, _);
    //@ public_chars(plaintext, 4, chars_of_int(sendr_val));
    //@ chars_to_integer(&sender);

    //@ close optional_crypto_chars(false, NA, NONCE_SIZE, cs_NA);
    memcpy((void*) plaintext + 4, NA, NONCE_SIZE);
    /*@ open optional_crypto_chars(false, (void*) plaintext + 4,
                                   NONCE_SIZE, cs_NA); @*/
    //@ close optional_crypto_chars(!collision_in_run, NB, NONCE_SIZE, cs_NB);
    memcpy((void*) plaintext + 4 + NONCE_SIZE, NB, NONCE_SIZE);
    /*@ open optional_crypto_chars(!collision_in_run,
                                   (void*) plaintext + prefix_size,
                                   NONCE_SIZE, cs_NB); @*/
    /*@ if (collision_in_run)
          crypto_chars((void*) plaintext + prefix_size, NONCE_SIZE, cs_NB); @*/
    //@ assert chars(plaintext, prefix_size, ?cs_temp);
    //@ public_chars(plaintext, prefix_size, cs_temp);
    //@ crypto_chars(plaintext, prefix_size, cs_temp);
    //@ crypto_chars_join(plaintext);
    //@ assert crypto_chars(plaintext, p_size, ?p_cs);
    //@ append_assoc(chars_of_int(sendr_val), cs_NA, cs_NB);
    //@ assert cs_temp == append(chars_of_int(sendr_val), cs_NA);
    //@ assert p_cs == append(cs_temp, cs_NB);
    auth_enc(&havege_state, key, plaintext,
             (unsigned int) p_size, (void*) message + 4);
    /*@ open cryptogram((void*) message + 4 + 16,
                        p_size, ?enc_cs, ?enc_cg); @*/
    /*@ if (!collision_in_run)
        {
          if (yahalom_public_key(recvr_val, r_id2))
          {
            take_append(4, chars_of_int(sendr_val), append(cs_NA, cs_NB));
            drop_append(4, chars_of_int(sendr_val), append(cs_NA, cs_NB));
            take_append(NONCE_SIZE, cs_NA, cs_NB);
            drop_append(NONCE_SIZE, cs_NA, cs_NB);
            crypto_chars_split(plaintext, 4);
            crypto_chars_split(plaintext + 4, NONCE_SIZE);
            public_crypto_chars(plaintext, 4, chars_of_int(sendr_val));
            public_crypto_chars((void*) plaintext + 4, NONCE_SIZE, cs_NA);
            public_crypto_chars((void*) plaintext + 4 + NONCE_SIZE,
                                NONCE_SIZE, cs_NB);
            chars_join(plaintext + 4);
            chars_join(plaintext);
            public_chars(plaintext, p_size, p_cs);
            crypto_chars(plaintext, p_size, p_cs);
          }
          else
          {
            close yahalom_pub_msg1(server, sender, cg_NA, cg_NB);
          }
          close yahalom_pub(enc_cg);
          leak yahalom_pub(enc_cg);
          close cryptogram((void*) message + 4 + 16, p_size, enc_cs, enc_cg);
          public_cryptogram((void*) message + 4 + 16, enc_cg);
        }
    @*/
    //@ chars_join((void*) message + 4);
    //@ chars_join(message);
    net_send(&socket_out, message, (unsigned int) m_size);

    //@ close optional_crypto_chars(true, plaintext, p_size, _);
    zeroize(plaintext, p_size);
    free(message);
    free(plaintext);
  }

  {
    // 4. A -> B. ENC(KB, {A, KAB}), ENC(KAB, NB)
    int size1 = 4 + KEY_SIZE;
    int size2 = NONCE_SIZE;
    int size = 16 + size1 + 16 + size2;
    char *msg = malloc(size); if (msg == 0) abort();
    char *dec1 = malloc(size1); if (dec1 == 0) abort();
    char *dec2 = malloc(size2); if (dec2 == 0) abort();
    net_recv(&socket_in, msg, (unsigned int) size);

    auth_dec(key, (void*) msg, (unsigned int) size1, dec1);
    //@ open optional_crypto_chars(!collision_in_run, dec1, size1, ?cs_dec1);
    {
      /*@ if(collision_in_run)
          {
            chars_split(dec1, 4);
          }
          else
          {
            open exists(?enc_cg);
            open [_]yahalom_pub(enc_cg);
            crypto_chars_split(dec1, 4);
          }
      @*/
      //@ integer_to_chars(&sender);
      /*@ close optional_crypto_chars(false, (void*) &sender,
                                      4, chars_of_int(sendr_val)); @*/
      //@ close optional_crypto_chars(!collision_in_run, dec1, 4, _);
      if (memcmp(dec1, (void*) &sender, 4) != 0) abort();
      //@ open optional_crypto_chars(!collision_in_run, dec1, 4, _);
      //@ chars_to_integer(&sender);
      /*@ close optional_crypto_chars(!collision_in_run,
                                      dec1 + 4, KEY_SIZE, ?cs_KAB); @*/
      memcpy(generated_key, dec1 + 4, KEY_SIZE);
      /*@ open optional_crypto_chars(!collision_in_run,
                                     dec1 + 4, KEY_SIZE, cs_KAB); @*/
      //@ cg_KAB = chars_for_cg_sur_symmetric_key(cs_KAB);
      /*@ if(collision_in_run || yahalom_public_key(recvr_val, r_id2))
          {
            if (collision_in_run)
            {
              public_chars(generated_key, KEY_SIZE, cs_KAB);
              chars_join(dec1);
            }
            else
            {
              crypto_chars_join(dec1);
              public_crypto_chars(dec1, size1, cs_dec1);
              chars_split(dec1, 4);
              public_chars(dec1 + 4, KEY_SIZE, cs_KAB);
              public_chars_extract(dec1 + 4, cg_KAB);
              chars_join(dec1);
              crypto_chars(dec1, size1, cs_dec1);
            }
          }
          else
          {
            crypto_chars_join(dec1);
            assert [_]yahalom_pub_msg3(?server2, ?sender2, ?KAB2, ?s2,
                                       ?a_id2, ?r2, ?b_id2);
            take_append(4, chars_of_int(sendr_val), cs_KAB);
            take_append(4, chars_of_int(sender2), chars_for_cg(KAB2));
            drop_append(4, chars_of_int(sendr_val), cs_KAB);
            drop_append(4, chars_of_int(sender2), chars_for_cg(KAB2));
            assert server2 == server;
            chars_of_int_injective(sender2, sender);
            assert sender2 == sender;
            cg_KAB = KAB2;
            assert cg_KAB == cg_symmetric_key(server, _);
          }
      @*/
      //@ close cryptogram(generated_key, KEY_SIZE, cs_KAB, cg_KAB);
    }

    auth_dec(generated_key, msg + 16 + size1, (unsigned int) size2, dec2);
    //@ open optional_crypto_chars(!collision_in_run, dec2, size2, ?cs_dec2);
    {
      //@ close optional_crypto_chars(!collision_in_run, NB, NONCE_SIZE, _);
      //@ close optional_crypto_chars(!collision_in_run, dec2, size2, _);
      if (memcmp(dec2, NB, NONCE_SIZE) != 0) abort();
      //@ close optional_crypto_chars(!collision_in_run, NB, NONCE_SIZE, cs_NB);
      /*@ if (!collision_in_run && !bad(server) &&
              !bad(sender) && !bad(receiver))
          {
            open exists(?enc_cg);
            open [_]yahalom_pub(enc_cg);
            assert [_]yahalom_pub_msg4(?server2, ?sender2,
                                       ?receiver2, ?a_id2, ?NB2);
            assert NB2 == cg_random(?b2, ?b_id2);
            chars_for_cg_inj_random(cg_NB, NB2);
            if (bad(server2) || bad(sender2) || bad(receiver2))
            {
              open [_]yahalom_pub(cg_NB);
              assert false;
            }
          }
      @*/
    }

    free(msg);
    /*@ close optional_crypto_chars(!collision_in_run, dec1,
                                    size1, cs_dec1); @*/
    zeroize(dec1, size1);
    free(dec1);
    zeroize(dec2, size2);
    free(dec2);
  }

  zeroize(NB, NONCE_SIZE);

  havege_free(&havege_state);
  //@ open havege_state(&havege_state);

  net_close(socket);
  net_close(socket_in);
  net_close(socket_out);
}
