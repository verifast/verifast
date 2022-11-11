#include "yahalom.h"

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

//@ #include "quantifiers.gh"

#define SENDER_PORT 121212
#define RECVER_PORT 232323
#define SERVER_PORT 343434

#define INCLUDE_SERVER
#define INCLUDE_SENDER
#define INCLUDE_RECEIVER

void encrypt(havege_state *state, char *key, char *msg,
             unsigned int msg_len, char* output)
/*@ requires [_]public_invar(yahalom_pub) &*&
             havege_state_initialized(state) &*&
             principal(?principal1, _) &*&
             [?f1]cryptogram(key, KEY_SIZE, ?key_ccs, ?key_cg) &*&
               key_cg == cg_symmetric_key(?principal2, ?id) &*&
             [?f2]crypto_chars(?kind, msg, msg_len, ?msg_ccs) &*&
               1024 >= msg_len &*&
               msg_len >= MINIMAL_STRING_SIZE &*&
             chars_(output, 16 + msg_len, _); @*/
/*@ ensures  havege_state_initialized(state) &*&
             principal(principal1, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_ccs, key_cg) &*&
             [f2]crypto_chars(kind, msg, msg_len, msg_ccs) &*&
             crypto_chars(normal, output, 16, ?iv_ccs) &*&
             cryptogram(output + 16, msg_len, _, ?enc_cg) &*&
             enc_cg == cg_aes_encrypted(principal2, id, msg_ccs, iv_ccs); @*/
{
  //@ open principal(principal1, _);
  char iv[16];
  aes_context aes_context;
  size_t iv_off = 0;
  //@ chars__limits(output);

  //@ close random_request(principal1, IP(0, 0), false);
  if (havege_random(state, iv, 16) != 0) abort();
  //@ open cryptogram(iv, 16, ?iv_ccs, ?iv_cg);
  //@ close yahalom_pub(iv_cg);
  //@ leak yahalom_pub(iv_cg);
  crypto_memcpy(output, iv, 16);
  //@ close cryptogram(output, 16, iv_ccs, iv_cg);
  //@ public_cryptogram(output, iv_cg);

  //@ close aes_context(&aes_context);
  if (aes_setkey_enc(&aes_context, key, (unsigned int) KEY_SIZE * 8) != 0)
    abort();
  if (aes_crypt_cfb128(&aes_context, AES_ENCRYPT,
                       (unsigned int) msg_len,
                       &iv_off, iv, msg, output + 16) != 0)
    abort();
  zeroize(iv, 16);
  aes_free(&aes_context);
  //@ open aes_context(&aes_context);
  //@ chars_to_crypto_chars(output, 16);
  //@ assert cryptogram(output + 16, msg_len, ?enc_cs, ?enc_cg);
  //@ assert enc_cg == cg_aes_encrypted(principal2, id, msg_ccs, iv_ccs);
  //@ close principal(principal1, _);
}

void decrypt(char *key, char *msg, unsigned int msg_len, char* output)
/*@ requires [_]public_invar(yahalom_pub) &*&
             decryption_pre(true, false, ?principal1, ?s, ?msg_ccs) &*&
             random_permission(principal1, _) &*&
             [?f1]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
               key_cg == cg_symmetric_key(?principal2, ?id) &*&
             [?f2]crypto_chars(normal, msg, 16, ?iv_ccs) &*&
             [f2]crypto_chars(normal, msg + 16, msg_len, msg_ccs) &*&
               msg_len >= MINIMAL_STRING_SIZE &*& msg_len < 1024 &*&
             chars_(output, msg_len, _); @*/
/*@ ensures  decryption_post(true, ?garbage, principal1,
                             s, principal2, id, ?dec_ccs) &*&
             random_permission(principal1, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_cs, key_cg) &*&
             [f2]crypto_chars(normal, msg, 16 + msg_len, append(iv_ccs, msg_ccs)) &*&
             crypto_chars(?kind, output, msg_len, dec_ccs) &*&
             exists(?enc_cg) &*& [_]yahalom_pub(enc_cg) &*&
             msg_ccs == ccs_for_cg(enc_cg) &*&
             enc_cg == cg_aes_encrypted(?p, ?c, ?dec_ccs2, ?iv_ccs2) &*&
             garbage ?
               kind == normal
             :
               kind == secret &*&
               p == principal2 &*& c == id &*&
               dec_ccs == dec_ccs2 && iv_ccs == iv_ccs2; @*/
{
  char iv[16];
  aes_context aes_context;
  size_t iv_off = 0;
  //@ crypto_chars_limits(msg);

  //@ cryptogram iv_cg = ccs_for_cg_sur(iv_ccs, tag_nonce);
  //@ crypto_chars_to_chars(msg, 16);
  //@ assert [f2]chars(msg, 16, ?iv_cs);
  //@ public_cs(iv_cs);
  //@ public_ccs_cg(iv_cg);
  //@ chars_to_secret_crypto_chars(msg, 16);
  crypto_memcpy(iv, msg, 16);
  //@ public_crypto_chars(msg, 16);
  //@ assert [f2]chars(msg, 16, ?iv_cs0);
  //@ cs_to_ccs_inj(iv_cs, iv_cs0);

  //@ close aes_context(&aes_context);
  if (aes_setkey_enc(&aes_context, key, (unsigned int) KEY_SIZE * 8) != 0)
    abort();
  //@ crypto_chars_to_chars(msg + 16, msg_len);
  //@ assert [f2]chars(msg + 16, msg_len, ?msg_cs);
  //@ interpret_encrypted(msg + 16, msg_len);
  //@ open [f2]cryptogram(msg + 16, msg_len, msg_ccs, ?enc_cg);
  //@ close [f2]cryptogram(msg + 16, msg_len, msg_ccs, enc_cg);
  //@ assert enc_cg == cg_aes_encrypted(?p, ?c, ?pay_ccs2, ?iv_ccs2);
  //@ open [_]yahalom_pub(enc_cg);
  //@ close exists(enc_cg);
  if (aes_crypt_cfb128(&aes_context, AES_DECRYPT,
                       (unsigned int) msg_len,
                       &iv_off, iv, msg + 16, output) != 0)
    abort();
  //@ public_cryptogram(msg + 16, enc_cg);
  //@ assert [f2]chars(msg + 16, msg_len, ?msg_cs0);
  //@ cs_to_ccs_inj(msg_cs, msg_cs0);
  zeroize(iv, 16);
  aes_free(&aes_context);
  //@ open aes_context(&aes_context);
  //@ chars_join(msg);
  //@ cs_to_ccs_append(iv_cs, msg_cs);
  //@ chars_to_crypto_chars(msg, 16 + msg_len);
}

#ifdef INCLUDE_SERVER

void server(int server, int sender, int receiver,
            char *s_key, char *r_key)
/*@ requires [_]public_invar(yahalom_pub) &*&
             [_]decryption_key_classifier(yahalom_public_key) &*&
             principal(server, _) &*&
             [?f1]cryptogram(s_key, KEY_SIZE, ?s_key_ccs, ?s_key_cg) &*&
               s_key_cg == cg_symmetric_key(sender, ?s_id) &*&
               cg_info(s_key_cg) == int_pair(3, server) &*&
             [?f2]cryptogram(r_key, KEY_SIZE, ?r_key_ccs, ?r_key_cg) &*&
               r_key_cg == cg_symmetric_key(receiver, ?r_id) &*&
               cg_info(r_key_cg) == int_pair(3, server); @*/
/*@ ensures  [_]public_invar(yahalom_pub) &*&
             principal(server, _) &*&
             [f1]cryptogram(s_key, KEY_SIZE, s_key_ccs, s_key_cg) &*&
             [f2]cryptogram(r_key, KEY_SIZE, r_key_ccs, r_key_cg); @*/
{
  //@ open principal(server, _);
  int socket;
  int socket_in;
  int socket_out;
  havege_state havege_state;
  char NA[NONCE_SIZE];
  //@ cryptogram NB_cg;
  char NB[NONCE_SIZE];
  //@ cryptogram NA_cg;
  char KAB[KEY_SIZE];
  //@ bool condition;

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

  //@ close havege_state(&havege_state);
  havege_init(&havege_state);

  {
    // 2. B -> S. B, ENC(KB, {A, NA, NB})
    int prefix_size = ID_SIZE + NONCE_SIZE;
    int d_size = prefix_size + NONCE_SIZE;
    char *decrypted = malloc((size_t)d_size); if (decrypted == 0) abort();
    int m_size = ID_SIZE + 16 + d_size;
    char *message = malloc((size_t)m_size); if (message == 0) abort();

    // Receive the message
    if (net_recv(&socket_in, message, (unsigned int) m_size) != m_size)
      abort();
    //@ chars_split(message, ID_SIZE);
    //@ chars_split(message + ID_SIZE, 16);
    //@ assert chars(message, ID_SIZE, ?r_id_cs);
    //@ public_chars(message, ID_SIZE);
    //@ assert chars(message + ID_SIZE, 16, ?iv_cs);
    //@ chars_to_crypto_chars(message + ID_SIZE, 16);
    //@ assert crypto_chars(normal, message + ID_SIZE, 16, ?iv_ccs);
    //@ assert chars(message + ID_SIZE + 16, d_size, ?enc_cs);
    //@ chars_to_crypto_chars(message, ID_SIZE);
    //@ chars_to_crypto_chars(message + ID_SIZE + 16, d_size);
    //@ assert crypto_chars(normal, message + ID_SIZE + 16, d_size, ?enc_ccs);
    //@ close check_identifier_ghost_args(true, false, 0, 0, 0, append(iv_ccs, enc_ccs));
    check_identifier(message, receiver);
    //@ cs_to_ccs_crypto_chars(message, identifier(receiver));
    //@ assert chars(message, ID_SIZE, ?r_id_cs');
    //@ cs_to_ccs_inj(r_id_cs, r_id_cs');
    //@ assert r_id_cs == identifier(receiver);
    //@ list<crypto_char> sid_ccs = cs_to_ccs(identifier(sender));
    //@ structure s = known_value(0, sid_ccs);
    //@ close decryption_pre(true, false, server, s, enc_ccs);
    decrypt(r_key, (void*) message + ID_SIZE, (unsigned int) d_size, decrypted);
    //@ crypto_chars_to_chars(message + ID_SIZE, 16 + d_size);
    //@ open [_]yahalom_pub(?enc_cg);
    /*@ open decryption_post(true, ?garbage, server, s,
                             receiver, r_id, ?dec_ccs); @*/
    //@ crypto_chars_split(decrypted, ID_SIZE);
    //@ crypto_chars_split((void*) decrypted + ID_SIZE, NONCE_SIZE);
    crypto_memcpy(NA, (void*) decrypted + ID_SIZE, NONCE_SIZE);
    crypto_memcpy(NB, (void*) decrypted + prefix_size, NONCE_SIZE);
    //@ assert crypto_chars(?kind, decrypted, ID_SIZE, ?id_ccs);
    //@ assert crypto_chars(kind, decrypted + ID_SIZE, NONCE_SIZE, ?NA_ccs);
    /*@ assert crypto_chars(kind, (void*) decrypted + ID_SIZE + NONCE_SIZE,
                                   NONCE_SIZE, ?NB_ccs); @*/
    //@ NA_cg = ccs_for_cg_sur(NA_ccs, tag_nonce);
    //@ NB_cg = ccs_for_cg_sur(NB_ccs, tag_nonce);
    //@ condition = col || yahalom_public_key(receiver, r_id, true);
    /*@ if (col || garbage || condition)
        {
          if (col || garbage)
          {
            crypto_chars_to_chars(decrypted, ID_SIZE);
            crypto_chars_to_chars(decrypted + ID_SIZE, NONCE_SIZE);
            public_chars(decrypted + ID_SIZE, NONCE_SIZE);
            chars_to_crypto_chars(decrypted + ID_SIZE, NONCE_SIZE);
            crypto_chars_to_chars(decrypted + ID_SIZE + NONCE_SIZE, NONCE_SIZE);
            public_chars(decrypted + ID_SIZE + NONCE_SIZE, NONCE_SIZE);
            chars_to_crypto_chars(decrypted + ID_SIZE + NONCE_SIZE, NONCE_SIZE);
          }
          else
          {
            public_ccs_split(dec_ccs, ID_SIZE);
            public_ccs_split(append(NA_ccs, NB_ccs), NONCE_SIZE);
            public_crypto_chars(decrypted, ID_SIZE);
          }
          public_crypto_chars(NA, NONCE_SIZE);
          public_crypto_chars(NB, NONCE_SIZE);
          chars_to_crypto_chars(NB, NONCE_SIZE);
          public_ccs_cg(NB_cg);
        }
        else
        {
          assert [_]yahalom_pub_msg1(_, ?s2, ?NA2, ?NB2);
          take_append(ID_SIZE, cs_to_ccs(identifier(s2)),
                      append(ccs_for_cg(NA2), ccs_for_cg(NB2)));
          public_crypto_chars(decrypted, ID_SIZE);
        }
    @*/
    //@ chars_to_crypto_chars(decrypted, ID_SIZE);
    /*@ close check_identifier_ghost_args(true, garbage, server, receiver,
                                          r_id, append(NA_ccs, NB_ccs)); @*/
    check_identifier(decrypted, sender);
    //@ crypto_chars_join((void*) decrypted + ID_SIZE);
    /*@ if (!col && !garbage)
        {
          crypto_chars_to_chars(decrypted, ID_SIZE);
          chars_to_secret_crypto_chars(decrypted, ID_SIZE);
        }
    @*/
    //@ crypto_chars_join(decrypted);
    /*@ if (!col && !garbage && !condition)
        {
          assert [_]yahalom_pub_msg1(?srv2, ?s2, ?NA2, ?NB2);
          take_append(ID_SIZE, sid_ccs, append(NA_ccs, NB_ccs));
          take_append(ID_SIZE, cs_to_ccs(identifier(s2)),
                               append(ccs_for_cg(NA2), ccs_for_cg(NB2)));
          drop_append(ID_SIZE, cs_to_ccs(identifier(sender)), append(NA_ccs, NB_ccs));
          drop_append(ID_SIZE, cs_to_ccs(identifier(s2)),
                               append(ccs_for_cg(NA2), ccs_for_cg(NB2)));
          take_append(NONCE_SIZE, NA_ccs, NB_ccs);
          take_append(NONCE_SIZE, ccs_for_cg(NA2), ccs_for_cg(NB2));
          drop_append(NONCE_SIZE, NA_ccs, NB_ccs);
          drop_append(NONCE_SIZE, ccs_for_cg(NA2), ccs_for_cg(NB2));
          assert srv2 == server;
          cs_to_ccs_inj(identifier(s2), identifier(sender));
          equal_identifiers(s2, sender);
          assert s2 == sender;
          assert ccs_for_cg(NA2) == NA_ccs;
          NA_cg = NA2;
          close cryptogram(NA, NONCE_SIZE, NA_ccs, NA_cg);
          public_cryptogram(NA, NA_cg);
          assert ccs_for_cg(NB2) == NB_ccs;
          NB_cg = NB2;
          assert NB_cg == cg_nonce(receiver, _);
        }
    @*/

    zeroize(decrypted, d_size);
    free(decrypted);
    //@ chars_join(message);
    free(message);
  }

  //@ chars_to_crypto_chars(NA, NONCE_SIZE);
  //@ assert crypto_chars(normal, NA, NONCE_SIZE, ?ccs_NA);
  //@ assert ccs_NA == ccs_for_cg(NA_cg);
  //@ assert NA_cg == cg_nonce(?s2, ?a_id);
  //@ public_ccs_cg(NA_cg);
  //@ assert true == cg_is_gen_or_pub(NA_cg);
  //@ assert crypto_chars(_, NB, NONCE_SIZE, ?ccs_NB);
  //@ assert ccs_NB == ccs_for_cg(NB_cg);
  //@ assert NB_cg == cg_nonce(?r2, ?b_id);
  /*@ close random_request(server, IP(4, IP(sender, IP(receiver,
                                   IP(s2, IP(a_id, IP(r2, b_id)))))), true); @*/

  if (havege_random(&havege_state, KAB, KEY_SIZE) != 0) abort();
  //@ open cryptogram(KAB, KEY_SIZE, ?ccs_KAB, ?cg_KAB);
  //@ assert cg_KAB == cg_symmetric_key(server, ?id_KAB);
  /*@ if (yahalom_public_key(server, id_KAB, true))
      {
        close cryptogram(KAB, KEY_SIZE, ccs_KAB, cg_KAB);
        close yahalom_pub(cg_KAB);
        leak yahalom_pub(cg_KAB);
        public_cryptogram(KAB, cg_KAB);
        public_chars(KAB, KEY_SIZE);
        chars_to_secret_crypto_chars(KAB, KEY_SIZE);
        assert [_]public_ccs(ccs_KAB);
      }
  @*/

  {
    // 3. S -> A. ENC(KA, {B, KAB, NA, NB}), ENC(KB, {A, KAB})
    int size1 = 16 + ID_SIZE + KEY_SIZE + NONCE_SIZE + NONCE_SIZE;
    int size2 = 16 + ID_SIZE + KEY_SIZE;
    char *enc1 = malloc((size_t)size1); if (enc1 == 0) abort();
    char *enc2 = malloc((size_t)size2); if (enc2 == 0) abort();
    {
      //ENC(KA, {B, KAB, NA, NB})
      int s = ID_SIZE + KEY_SIZE + NONCE_SIZE + NONCE_SIZE;
      char* m = malloc((size_t)s); if (m == 0) abort();
      write_identifier(m, receiver);
      //@ cs_to_ccs_crypto_chars(m, identifier(receiver));
      //@ chars_to_secret_crypto_chars(m, ID_SIZE);
      //@ list<crypto_char> rid_ccs = cs_to_ccs(identifier(receiver));
      //@ assert crypto_chars(secret, m, ID_SIZE, rid_ccs);
      crypto_memcpy(m + ID_SIZE, KAB, KEY_SIZE);
      //@ crypto_chars_to_chars(NA, NONCE_SIZE);
      //@ chars_to_secret_crypto_chars(NA, NONCE_SIZE);
      crypto_memcpy(m + ID_SIZE + KEY_SIZE, NA, NONCE_SIZE);
      //@ public_crypto_chars(NA, NONCE_SIZE);
      /*@ if (col || yahalom_public_key(receiver, r_id, true))
          {
            crypto_chars_to_chars(NB, NONCE_SIZE);
            chars_to_secret_crypto_chars(NB, NONCE_SIZE);
          }
      @*/
      crypto_memcpy(m + ID_SIZE + KEY_SIZE + NONCE_SIZE, NB, NONCE_SIZE);
      //@ crypto_chars_join(m + ID_SIZE + KEY_SIZE);
      //@ crypto_chars_join(m + ID_SIZE);
      //@ crypto_chars_join(m);
      //@ close principal(server, _);
      encrypt(&havege_state, s_key, m,
              (unsigned int) (ID_SIZE + KEY_SIZE + NONCE_SIZE + NONCE_SIZE), enc1);
      //@ open cryptogram(enc1 + 16, s, ?enc_ccs, ?enc_cg);
      /*@ if (!col)
          {
            list <crypto_char> dec_ccs = append(rid_ccs, append(ccs_KAB,
                                                append(ccs_NA, ccs_NB)));
            assert enc_cg == cg_aes_encrypted(sender, s_id, dec_ccs, ?ent);

            if (yahalom_public_key(sender, s_id, true))
            {
              assert true == yahalom_public_key(server, id_KAB, true);
              take_append(ID_SIZE, rid_ccs, append(ccs_KAB,
                                                   append(ccs_NA, ccs_NB)));
              drop_append(ID_SIZE, rid_ccs, append(ccs_KAB,
                                                   append(ccs_NA, ccs_NB)));
              take_append(KEY_SIZE, ccs_KAB, append(ccs_NA, ccs_NB));
              drop_append(KEY_SIZE, ccs_KAB, append(ccs_NA, ccs_NB));
              take_append(NONCE_SIZE, ccs_NA, ccs_NB);
              crypto_chars_split(m, ID_SIZE);
              crypto_chars_split(m + ID_SIZE, KEY_SIZE);
              crypto_chars_split(m + ID_SIZE + KEY_SIZE, NONCE_SIZE);
              public_crypto_chars(m, ID_SIZE);
              close yahalom_pub(cg_KAB);
              leak yahalom_pub(cg_KAB);
              close cryptogram(m + ID_SIZE, KEY_SIZE, ccs_KAB, cg_KAB);
              public_cryptogram(m + ID_SIZE, cg_KAB);
              public_crypto_chars(m + ID_SIZE + KEY_SIZE, NONCE_SIZE);
              if (condition)
              {
                public_crypto_chars(m + ID_SIZE + KEY_SIZE + NONCE_SIZE,
                                    NONCE_SIZE);
              }
              else
              {
                close yahalom_pub(NB_cg);
                leak yahalom_pub(NB_cg);
                close cryptogram(m + ID_SIZE + KEY_SIZE + NONCE_SIZE,
                                 NONCE_SIZE, ccs_NB, NB_cg);
                public_cryptogram(m + ID_SIZE + KEY_SIZE + NONCE_SIZE, NB_cg);
              }
              assert chars(m, ID_SIZE, ?rid_cs);
              assert chars(m + ID_SIZE, KEY_SIZE, ?KAB_cs);
              assert chars(m + ID_SIZE + KEY_SIZE, NONCE_SIZE, ?NA_cs);
              assert chars(m + ID_SIZE + KEY_SIZE + NONCE_SIZE, NONCE_SIZE, ?NB_cs);
              public_ccs_cg(NB_cg);
              cs_to_ccs_append(NA_cs, NB_cs);
              cs_to_ccs_append(KAB_cs, append(NA_cs, NB_cs));
              cs_to_ccs_append(rid_cs, append(KAB_cs, append(NA_cs, NB_cs)));

              chars_join(m + ID_SIZE + KEY_SIZE);
              chars_join(m + ID_SIZE);
              chars_join(m);
              public_chars(m, s);
              chars_to_crypto_chars(m, s);
            }
            else
            {
              close yahalom_pub_msg2(server, receiver, NA_cg,
                                     NB_cg, cg_KAB);
            }
            close yahalom_pub(enc_cg);
            leak yahalom_pub(enc_cg);
            close cryptogram(enc1 + 16, ID_SIZE + KEY_SIZE + NONCE_SIZE + NONCE_SIZE,
                             enc_ccs, enc_cg);
            public_cryptogram(enc1 + 16, enc_cg);
          }
          else
          {
            crypto_chars_to_chars(enc1 + 16, s);
          }
      @*/
      //@ crypto_chars_to_chars(enc1, 16);
      //@ chars_join(enc1);
      //@ public_chars(enc1, s + 16);
      //@ chars_to_crypto_chars(enc1, s + 16);
      zeroize(m, ID_SIZE + KEY_SIZE + NONCE_SIZE + NONCE_SIZE);
      free(m);
    }

    {
      //ENC(KB, {A, KAB})
      int s = ID_SIZE + KEY_SIZE;
      char* m = malloc((size_t)s); if (m == 0) abort();
      write_identifier(m, sender);
      //@ crypto_chars_to_chars(m, ID_SIZE);
      //@ chars_to_secret_crypto_chars(m, ID_SIZE);
      //@ assert crypto_chars(secret, m, ID_SIZE, cs_to_ccs(identifier(sender)));
      crypto_memcpy(m + ID_SIZE, KAB, KEY_SIZE);
      //@ crypto_chars_join(m);

      encrypt(&havege_state, r_key, m, (unsigned int) (ID_SIZE + KEY_SIZE), enc2);
      //@ open cryptogram(enc2 + 16, ID_SIZE + KEY_SIZE, ?enc_ccs, ?enc_cg);
      /*@ if (!col)
          {
            assert enc_cg == cg_aes_encrypted(receiver, r_id,
              append(cs_to_ccs(identifier(sender)), ccs_KAB), ?ent);
            if (yahalom_public_key(receiver, r_id, true))
            {
              assert true == yahalom_public_key(server, id_KAB, true);
              take_append(ID_SIZE, cs_to_ccs(identifier(sender)), ccs_KAB);
              drop_append(ID_SIZE, cs_to_ccs(identifier(sender)), ccs_KAB);
              crypto_chars_split(m, ID_SIZE);
              public_crypto_chars(m, ID_SIZE);
              close cryptogram(m + ID_SIZE, KEY_SIZE, ccs_KAB, cg_KAB);
              close yahalom_pub(cg_KAB);
              leak yahalom_pub(cg_KAB);
              public_cryptogram(m + ID_SIZE, cg_KAB);

              assert chars(m, ID_SIZE, ?sid_cs);
              assert chars(m + ID_SIZE, KEY_SIZE, ?KAB_cs);
              cs_to_ccs_append(sid_cs, KAB_cs);

              chars_join(m);
              public_chars(m, s);
              chars_to_crypto_chars(m, s);
            }
            else
            {
              close yahalom_pub_msg3(server, sender, cg_KAB,
                                     s2, a_id, r2, b_id);
            }
            close yahalom_pub(enc_cg);
            leak yahalom_pub(enc_cg);
            close cryptogram(enc2 + 16, ID_SIZE + KEY_SIZE, enc_ccs, enc_cg);
            public_cryptogram(enc2 + 16, enc_cg);
          }
          else
          {
            crypto_chars_to_chars(enc2 + 16, s);
          }
      @*/
      //@ crypto_chars_to_chars(enc2, 16);
      //@ chars_join(enc2);
      //@ public_chars(enc2, s + 16);
      //@ chars_to_crypto_chars(enc2, s + 16);
      zeroize(m, ID_SIZE + KEY_SIZE);
      free(m);
    }

    {
      int size = size1 + size2;
      char *message = malloc((size_t)size); if (message == 0) abort();
      crypto_memcpy(message, enc1, (unsigned int) size1);
      crypto_memcpy(message + size1, enc2, (unsigned int) size2);
      //@ crypto_chars_join(message);
      //@ crypto_chars_to_chars(message, size);
      //@ open principal(server, _);
      net_send(&socket_out, message, (unsigned int) size);

      free(message);
    }

    //@ crypto_chars_to_chars(enc1, size1);
    //@ crypto_chars_to_chars(enc2, size2);
    free(enc1);
    free(enc2);
  }

  havege_free(&havege_state);
  //@ open havege_state(&havege_state);

  zeroize(KAB, KEY_SIZE);
  zeroize(NB, NONCE_SIZE);

  net_close(socket);
  net_close(socket_in);
  net_close(socket_out);
  //@ close principal(server, _);
}

#endif
#ifdef INCLUDE_SENDER

void sender(int server, int sender, int receiver,
            char *key, char *generated_key)
/*@ requires [_]public_invar(yahalom_pub) &*&
             [_]decryption_key_classifier(yahalom_public_key) &*&
             principal(sender, ?s_id) &*&
             [?f]cryptogram(key, KEY_SIZE, ?key_ccs, ?key_cg) &*&
               key_cg == cg_symmetric_key(sender, ?s_id2) &*&
               cg_info(key_cg) == IP(3, server) &*&
             chars_(generated_key, KEY_SIZE, _); @*/
/*@ ensures  principal(sender, _) &*&
             [f]cryptogram(key, KEY_SIZE, key_ccs, key_cg) &*&
             cryptogram(generated_key, KEY_SIZE, _, ?g_key_cg) &*&
             col || bad(server) || bad(sender) ?
               true
             :
               g_key_cg == cg_symmetric_key(server, ?id) &*&
               IF(cg_info(g_key_cg)) == 4 &*&
               IF(IS(cg_info(g_key_cg))) == sender &*&
               IF(IS(IS(cg_info(g_key_cg)))) == receiver &*&
               IF(IS(IS(IS(cg_info(g_key_cg))))) == sender &*&
               IF(IS(IS(IS(IS(cg_info(g_key_cg)))))) ==  s_id + 1 &*&
               bad(receiver) ||
                 IF(IS(IS(IS(IS(IS(cg_info(g_key_cg))))))) == receiver &&
                 !yahalom_public_key(server, id, true); @*/
{
  //@ open principal(sender, s_id);
  //@ list<char> rid_cs = identifier(receiver);
  //@ list<crypto_char> rid_ccs = cs_to_ccs(rid_cs);
  int socket;
  int socket_in;
  int socket_out;
  havege_state havege_state;
  char NA[NONCE_SIZE];
  char NB[NONCE_SIZE];
  char *MB;
  //@ cryptogram cg_NA2;
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

  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  //@ close random_request(sender, int_pair(1, int_pair(sender, receiver)), false);
  if (havege_random(&havege_state, NA, NONCE_SIZE) != 0) abort();
  //@ open cryptogram(NA, NONCE_SIZE, ?ccs_NA, ?cg_NA);
  //@ close cryptogram(NA, NONCE_SIZE, ccs_NA, cg_NA);
  //@ assert cg_NA == cg_nonce(sender, s_id + 1);
  //@ close yahalom_pub(cg_NA);
  //@ leak yahalom_pub(cg_NA);
  //@ public_cryptogram(NA, cg_NA);
  //@ public_chars(NA, NONCE_SIZE);
  //@ chars_to_crypto_chars(NA, NONCE_SIZE);

  {
    // 1. A -> B. A, NA
    char* message = malloc((size_t)(ID_SIZE + NONCE_SIZE)); if (message == 0) abort();

    write_identifier(message, sender);
    //@ crypto_chars_split(message, ID_SIZE);
    crypto_memcpy((void*) message + ID_SIZE, NA, NONCE_SIZE);
    //@ crypto_chars_join(message);
    //@ crypto_chars_join(message);
    //@ crypto_chars_to_chars(message, ID_SIZE + NONCE_SIZE);
    net_send(&socket_out, message, (unsigned int) ID_SIZE + NONCE_SIZE);
    free(message);
  }

  {
    // 3. S -> A. ENC(KA, {B, KAB, NA, NB}), ENC(KB, {A, KAB})
    int size1 = ID_SIZE + KEY_SIZE + NONCE_SIZE + NONCE_SIZE;
    int size2 = 16 + ID_SIZE + KEY_SIZE;
    int size = 16 + size1 + size2;
    char *msg = malloc((size_t)size); if (msg == 0) abort();
    char *dec = malloc((size_t)size1); if (dec == 0) abort();
    MB = malloc((size_t)size2); if (MB == 0) abort();

    if (net_recv(&socket_in, msg, (unsigned int) size) != size)
      abort();
    //@ chars_split(msg, 16 + size1);
    //@ chars_to_crypto_chars(msg + 16 + size1, size2);
    crypto_memcpy(MB, msg + 16 + size1, (unsigned int) size2);
    //@ chars_split(msg, 16);
    //@ assert chars(msg, 16, ?iv_cs);
    //@ assert chars(msg + 16, size1, ?enc_cs);
    //@ chars_to_crypto_chars(msg + 16, size1);
    //@ assert crypto_chars(normal, msg + 16, size1, ?enc_ccs);
    //@ structure s = known_value(0, rid_ccs);
    //@ close decryption_pre(true, false, sender, s, enc_ccs);
    //@ chars_to_crypto_chars(msg, 16);
    decrypt(key, (void*) msg, (unsigned int) size1, dec);
    //@ open [_]yahalom_pub(?enc_cg);
    /*@ open decryption_post(true, ?garbage, sender, s,
                             sender, s_id2, ?dec_ccs); @*/
    //@ crypto_chars_to_chars(msg, 16 + size1);
    //@ crypto_chars_to_chars(msg + 16 + size1, size2);
    //@ chars_join(msg);
    free(msg);
    //@ assert crypto_chars(?kind, dec, size1, dec_ccs);
    //@ assert enc_cg == cg_aes_encrypted(?p2, ?c2, ?dec_ccs2, ?iv_ccs2);
    //@ crypto_chars_split(dec, ID_SIZE);
    //@ crypto_chars_split(dec + ID_SIZE, KEY_SIZE);
    //@ crypto_chars_split(dec + ID_SIZE + KEY_SIZE, NONCE_SIZE);
    //@ assert crypto_chars(kind, dec, ID_SIZE, ?id_ccs);
    //@ assert crypto_chars(kind, dec + ID_SIZE, KEY_SIZE, ?ccs_KAB);
    //@ assert crypto_chars(kind, dec + ID_SIZE + KEY_SIZE, NONCE_SIZE, ?ccs_NA2);
    /*@ assert crypto_chars(kind, dec + ID_SIZE + KEY_SIZE + NONCE_SIZE,
                            NONCE_SIZE, ?ccs_NB); @*/
    //@ list<crypto_char> dec_ccs0 = append(ccs_KAB, append(ccs_NA2, ccs_NB));
    /*@ take_append(ID_SIZE, id_ccs, append(ccs_KAB,
                    append(ccs_NA, ccs_NB))); @*/
    /*@ drop_append(ID_SIZE, id_ccs, append(ccs_KAB,
                    append(ccs_NA, ccs_NB))); @*/
    //@ take_append(KEY_SIZE, ccs_KAB, append(ccs_NA, ccs_NB));
    //@ drop_append(KEY_SIZE, ccs_KAB, append(ccs_NA, ccs_NB));
    //@ take_append(NONCE_SIZE, ccs_NA, ccs_NB);
    //@ drop_append(NONCE_SIZE, ccs_NA, ccs_NB);
    //@ take_append(NONCE_SIZE, ccs_NA, ccs_NB);
    //@ drop_append(NONCE_SIZE, ccs_NA, ccs_NB);
    //@ assert dec_ccs == append(id_ccs, dec_ccs0);

    //@ bool condition = col || yahalom_public_key(sender, s_id2, true);
    //@ cg_NA2 = ccs_for_cg_sur(ccs_NA2, tag_nonce);
    //@ cg_NB = ccs_for_cg_sur(ccs_NB, tag_nonce);
    //@ cg_KAB = ccs_for_cg_sur(ccs_KAB, tag_symmetric_key);
    crypto_memcpy(generated_key, (void*) dec + ID_SIZE, KEY_SIZE);
    crypto_memcpy(NB, (void*) dec + ID_SIZE + KEY_SIZE + NONCE_SIZE, NONCE_SIZE);
    /*@ if (col || garbage || condition)
        {
          if (col || garbage)
          {
            crypto_chars_to_chars(dec, ID_SIZE);
            crypto_chars_to_chars(dec + ID_SIZE, KEY_SIZE);
            crypto_chars_to_chars(dec + ID_SIZE + KEY_SIZE, NONCE_SIZE);
            crypto_chars_to_chars(dec + ID_SIZE + KEY_SIZE + NONCE_SIZE, NONCE_SIZE);
          }
          else
          {
            public_ccs_split(dec_ccs, ID_SIZE);
            public_ccs_split(dec_ccs0, KEY_SIZE);
            public_ccs_split(append(ccs_NA2, ccs_NB), NONCE_SIZE);
            public_crypto_chars(dec, ID_SIZE);
            public_crypto_chars(dec + ID_SIZE, KEY_SIZE);
            public_crypto_chars(dec + ID_SIZE + KEY_SIZE, NONCE_SIZE);
            public_crypto_chars(dec + ID_SIZE + KEY_SIZE + NONCE_SIZE, NONCE_SIZE);

          }
          public_chars(dec + ID_SIZE + KEY_SIZE + NONCE_SIZE, NONCE_SIZE);
          public_ccs_cg(cg_NB);
          public_chars((void*) dec + ID_SIZE, KEY_SIZE);
          public_ccs_cg(cg_KAB);
          chars_to_crypto_chars(dec + ID_SIZE, KEY_SIZE);
          chars_to_crypto_chars(dec + ID_SIZE + KEY_SIZE, NONCE_SIZE);
          public_chars(dec + ID_SIZE + KEY_SIZE + NONCE_SIZE, NONCE_SIZE);
          chars_to_crypto_chars(dec + ID_SIZE + KEY_SIZE + NONCE_SIZE, NONCE_SIZE);
          public_ccs(dec + ID_SIZE + KEY_SIZE, NONCE_SIZE);
          MEMCMP_CCS(ccs_NA2)
        }
        else
        {
          assert [_]yahalom_pub_msg2(?s2, ?r2, ?NA2, ?NB2, ?KAB);
          take_append(ID_SIZE, cs_to_ccs(identifier(r2)),
                      append(ccs_for_cg(KAB),
                      append(ccs_for_cg(NA2), ccs_for_cg(NB2))));
          drop_append(ID_SIZE, cs_to_ccs(identifier(r2)),
                      append(ccs_for_cg(KAB),
                      append(ccs_for_cg(NA2), ccs_for_cg(NB2))));
          take_append(KEY_SIZE, ccs_for_cg(KAB),
                      append(ccs_for_cg(NA2), ccs_for_cg(NB2)));
          drop_append(KEY_SIZE, ccs_for_cg(KAB),
                      append(ccs_for_cg(NA2), ccs_for_cg(NB2)));
          take_append(NONCE_SIZE, ccs_for_cg(NA2), ccs_for_cg(NB2));
          drop_append(NONCE_SIZE, ccs_for_cg(NA2), ccs_for_cg(NB2));
          public_crypto_chars(dec, ID_SIZE);
          close cryptogram(dec + ID_SIZE + KEY_SIZE, NONCE_SIZE, ccs_for_cg(NA2), NA2);
          public_cryptogram(dec + ID_SIZE + KEY_SIZE, NA2);
          chars_to_crypto_chars(dec + ID_SIZE + KEY_SIZE, NONCE_SIZE);
          public_ccs(dec + ID_SIZE + KEY_SIZE, NONCE_SIZE);
          MEMCMP_CCS(ccs_for_cg(NA2))
        }
    @*/
    //@ chars_to_crypto_chars(dec, ID_SIZE);
    //@ close check_identifier_ghost_args(true, garbage, sender, sender, s_id2, dec_ccs0);
    check_identifier(dec, receiver);
    //@ assert id_ccs == rid_ccs;
    //@ MEMCMP_PUB(NA)
    if (crypto_memcmp(NA, dec + ID_SIZE + KEY_SIZE, NONCE_SIZE) != 0) abort();
    //@ assert ccs_NA == ccs_NA2;
    //@ assert crypto_chars(kind, NB, NONCE_SIZE, ccs_NB);
    /*@ if (!col && !garbage && !condition)
        {
          assert [_]yahalom_pub_msg2(?server2, ?receiver2, ?NA2, ?NB2,
                                     ?KAB2);
          assert length(identifier(receiver2)) == ID_SIZE;
          cs_to_ccs_inj(identifier(receiver2), identifier(receiver));
          assert identifier(receiver2) == identifier(receiver);
          assert ccs_KAB == ccs_for_cg(KAB2);
          assert ccs_NA == ccs_for_cg(NA2);
          equal_identifiers(receiver2, receiver);
          assert receiver2 == receiver;
          cg_KAB = KAB2;
          assert cg_KAB == cg_symmetric_key(server, _);
          ccs_for_cg_inj(cg_NA, NA2);
          assert cg_NA == cg_nonce(?s2, ?a_id);
          assert NB2 == cg_nonce(?r2, ?b_id);
          cg_NB = NB2;
          ccs_for_cg_inj(cg_NB, NB2);
          assert ccs_for_cg(cg_NB) == ccs_NB;
          assert server2 == server;
          assert cg_info(cg_KAB) == IP(4, IP(sender, IP(receiver,
                                      IP(s2, IP(a_id, IP(r2, b_id))))));
          crypto_chars_to_chars(dec, ID_SIZE);
          chars_to_secret_crypto_chars(dec, ID_SIZE);
          crypto_chars_to_chars(dec + ID_SIZE + KEY_SIZE, NONCE_SIZE);
          chars_to_secret_crypto_chars(dec + ID_SIZE + KEY_SIZE, NONCE_SIZE);
        }
    @*/
    //@ assert crypto_chars(?k, generated_key, KEY_SIZE, ccs_KAB);
    /*@ if (k == normal)
        {
          crypto_chars_to_chars(generated_key, KEY_SIZE);
          chars_to_secret_crypto_chars(generated_key, KEY_SIZE);
        }
    @*/
    //@ close cryptogram(generated_key, KEY_SIZE, ccs_KAB, cg_KAB);
    //@ crypto_chars_join(dec + ID_SIZE + KEY_SIZE);
    //@ crypto_chars_join(dec + ID_SIZE);
    //@ crypto_chars_join(dec);
    zeroize(dec, size1);
    free(dec);
  }

  //@ assert crypto_chars(?k, NB, NONCE_SIZE, ?ccs_NB);
  /*@ if (k == normal)
      {
        crypto_chars_to_chars(NB, NONCE_SIZE);
        chars_to_secret_crypto_chars(NB, NONCE_SIZE);
      }
  @*/
  //@ assert crypto_chars(secret, NB, NONCE_SIZE, ccs_NB);
  //@ assert ccs_NB == ccs_for_cg(cg_NB);
  //@ open cryptogram(generated_key, KEY_SIZE, ?ccs_KAB, cg_KAB);
  //@ close cryptogram(generated_key, KEY_SIZE, ccs_KAB, cg_KAB);

  //@ assert cg_KAB == cg_symmetric_key(?p0, ?c0);
  //@ assert col || bad(sender) || bad(server) || p0 == server;
  //@ assert cg_NA == cg_nonce(?sender2, ?a_id);
  //@ assert col || (sender == sender2 && a_id == s_id + 1);

  //@ assert cg_NB == cg_nonce(?receiver2, ?b_id);
  /*@ assert col || bad(server) || bad(sender) ||
                    bad(receiver) || receiver == receiver2; @*/
  {
    // 4. A -> B. ENC(KB, {A, KAB}), ENC(KAB, NB)
    int size1 = 16 + ID_SIZE + KEY_SIZE;
    int size2 = 16 + NONCE_SIZE;
    char *enc2 = malloc((size_t)size2); if (enc2 == 0) abort();
    {
      //@ close principal(sender, _);
      encrypt(&havege_state, generated_key, NB, NONCE_SIZE, enc2);
      //@ open cryptogram(enc2 + 16, NONCE_SIZE, ?enc_ccs, ?enc_cg);
      /*@ if (!col)
          {
            if (yahalom_public_key(p0, c0, true))
            {
              if (bad(receiver))
              {
                assert [_]yahalom_pub(cg_NB);
                close cryptogram(NB, NONCE_SIZE, ccs_NB, cg_NB);
                public_cryptogram(NB, cg_NB);
                public_chars(NB, NONCE_SIZE);
                chars_to_crypto_chars(NB, NONCE_SIZE);
              }
            }
            else
            {
              if (bad(server) || bad(sender))
              {
                public_crypto_chars(NB, NONCE_SIZE);
                public_ccs_cg(cg_NB);
                chars_to_crypto_chars(NB, NONCE_SIZE);
              }
              close yahalom_pub_msg4(server, sender, receiver, a_id, cg_NB);
            }
            close yahalom_pub(enc_cg);
            leak yahalom_pub(enc_cg);
            close cryptogram(enc2 + 16, NONCE_SIZE, enc_ccs, enc_cg);
            public_cryptogram(enc2 + 16, enc_cg);
          }
          else
          {
            crypto_chars_to_chars(enc2 + 16, NONCE_SIZE);
          }
      @*/
      //@ crypto_chars_to_chars(enc2, 16);
      //@ chars_join(enc2);
      //@ chars_to_crypto_chars(enc2, size2);
    }

    {
      int size = size1 + size2;
      char *message = malloc((size_t)size); if (message == 0) abort();
      crypto_memcpy(message, MB, (unsigned int) size1);
      //@ crypto_chars_to_chars(MB, size1);
      crypto_memcpy(message + size1, enc2, (unsigned int) size2);
      //@ crypto_chars_to_chars(enc2, size2);
      //@ crypto_chars_join(message);
      //@ crypto_chars_to_chars(message, size);
      //@ open principal(sender, _);
      net_send(&socket_out, message, (unsigned int) size);
      free(message);
    }
    free(enc2);
  }

  //@ crypto_chars_to_chars(NA, NONCE_SIZE);
  zeroize(NB, NONCE_SIZE);
  free(MB);

  havege_free(&havege_state);
  //@ open havege_state(&havege_state);

  net_close(socket);
  net_close(socket_in);
  net_close(socket_out);
  //@ close principal(sender, _);
}

#endif
#ifdef INCLUDE_RECEIVER

void receiver_(int socket_in, int sender, int receiver, int server,
               char *key, char *generated_key, char* NA, char* NB)
  /*@ requires [_]public_invar(yahalom_pub) &*&
               [_]decryption_key_classifier(yahalom_public_key) &*&
               principal(receiver, _) &*&
               net_status(socket_in, ?ip, ?port, connected) &*&
               [?f1]cryptogram(key, KEY_SIZE, ?key_ccs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(receiver, ?r_id1) &*&
                 cg_info(key_cg) == int_pair(3, server) &*&
               chars_(generated_key, KEY_SIZE, _) &*&
               crypto_chars(?kna, NA, NONCE_SIZE, ?ccs_NA) &*&
                 exists(?cg_NA) &*& ccs_NA == ccs_for_cg(cg_NA) &*&
                 cg_NA == cg_nonce(?s, ?s_id) &*&
               cryptogram(NB, NONCE_SIZE, ?ccs_NB, ?cg_NB) &*&
                 cg_NB == cg_nonce(receiver, ?r_id0) &*&
                 cg_info(cg_NB) ==
                   IP(2, IP(server, IP(sender, IP(s, s_id)))); @*/
  /*@ ensures  principal(receiver, _) &*&
               net_status(socket_in, ip, port, connected) &*&
               [f1]cryptogram(key, KEY_SIZE, key_ccs, key_cg) &*&
               cryptogram(generated_key, KEY_SIZE, ?ccs_KAB, ?cg_KAB) &*&
               crypto_chars(kna, NA, NONCE_SIZE, ccs_NA) &*&
               cryptogram(NB, NONCE_SIZE, ccs_NB, cg_NB) &*&
               col || bad(server) || bad(sender) || bad(receiver) ?
                 true
               :
                 cg_KAB == cg_symmetric_key(server, ?id) &*&
                 IF(cg_info(cg_KAB)) == 4 &*&
                 IF(IS(cg_info(cg_KAB))) == sender &*&
                 IF(IS(IS(cg_info(cg_KAB)))) == receiver &*&
                 IF(IS(IS(IS(cg_info(cg_KAB))))) == sender &*&
                 IF(IS(IS(IS(IS(IS(cg_info(cg_KAB))))))) == receiver &*&
                 IS(IS(IS(IS(IS(IS(cg_info(cg_KAB))))))) == r_id0; @*/
{
  //@ open principal(receiver, _);
  // 4. A -> B. ENC(KB, {A, KAB}), ENC(KAB, NB)
  int size1 = ID_SIZE + KEY_SIZE;
  int size2 = NONCE_SIZE;
  int size = 16 + size1 + 16 + size2;
  char *msg = malloc((size_t)size); if (msg == 0) abort();
  char *dec1 = malloc((size_t)size1); if (dec1 == 0) abort();
  char *dec2 = malloc((size_t)size2); if (dec2 == 0) abort();
  if (net_recv(&socket_in, msg, (unsigned int) size) != size)
    abort();
  //@ chars_split(msg, 16);
  //@ chars_split(msg + 16, size1);
  //@ assert chars(msg, 16, ?iv_cs1);
  //@ assert chars(msg + 16, size1, ?enc_cs1);
  //@ chars_to_crypto_chars(msg + 16, size1);
  //@ assert crypto_chars(normal, msg + 16, size1, ?enc_ccs1);
  //@ structure s1 = known_value(0, cs_to_ccs(identifier(sender)));
  //@ close decryption_pre(true, false, receiver, s1, enc_ccs1);
  //@ chars_to_crypto_chars(msg, 16);
  decrypt(key, (void*) msg, (unsigned int) size1, dec1);
  //@ open [_]yahalom_pub(?enc_cg);
  //@ assert enc_cg == cg_aes_encrypted(?p, ?c, ?dec_ccs2, ?iv_ccs2);
  /*@ open decryption_post(true, ?garbage, receiver, s1,
                            receiver, r_id1, ?dec_ccs); @*/
  //@ assert crypto_chars(?kind, dec1, size1, ?cs_dec1);
  //@ crypto_chars_split(dec1, ID_SIZE);
  //@ assert crypto_chars(kind, dec1, ID_SIZE, ?cs_id1);
  //@ assert crypto_chars(kind, dec1 + ID_SIZE, KEY_SIZE, ?ccs_KAB);
  //@ take_append(ID_SIZE, cs_id1, ccs_KAB);
  //@ drop_append(ID_SIZE, cs_id1, ccs_KAB);
  //@ cryptogram cg_KAB = ccs_for_cg_sur(ccs_KAB, tag_symmetric_key);
  /*@ if (col || garbage || yahalom_public_key(receiver, r_id1, true))
      {
        if (col || garbage)
        {
          crypto_chars_to_chars(dec1, ID_SIZE);
          public_chars(dec1, ID_SIZE);
          crypto_chars_to_chars(dec1 + ID_SIZE, KEY_SIZE);
          public_chars(dec1 + ID_SIZE, KEY_SIZE);
        }
        else
        {
          public_ccs_split(dec_ccs, ID_SIZE);
          public_crypto_chars(dec1, ID_SIZE);
          public_crypto_chars(dec1 + ID_SIZE, KEY_SIZE);
        }
        public_ccs_cg(cg_KAB);
        chars_to_crypto_chars(dec1 + ID_SIZE, KEY_SIZE);
      }
      else
      {
        assert [_]yahalom_pub_msg3(?server2, ?sender2, ?KAB2, ?s2,
                                    ?a_id2, ?r2, ?b_id2);
        take_append(ID_SIZE, cs_to_ccs(identifier(sender2)),
                    ccs_for_cg(KAB2));
        drop_append(ID_SIZE, cs_to_ccs(identifier(sender2)),
                    ccs_for_cg(KAB2));
        public_crypto_chars(dec1, ID_SIZE);
      }
  @*/
  crypto_memcpy(generated_key, dec1 + ID_SIZE, KEY_SIZE);
  //@ chars_to_crypto_chars(dec1, ID_SIZE);
  /*@ close check_identifier_ghost_args(true, garbage, receiver, receiver,
                                        r_id1, ccs_KAB); @*/
  check_identifier(dec1, sender);
  /*@ if(!col && !yahalom_public_key(receiver, r_id1, true))
      {
        assert [_]yahalom_pub_msg3(?server2, ?sender2, ?KAB2, ?s2,
                                    ?a_id2, ?r2, ?b_id2);
        assert server2 == server;
        cs_to_ccs_inj(identifier(sender2), identifier(sender));
        equal_identifiers(sender2, sender);
        assert sender2 == sender;
        cg_KAB = KAB2;
        assert cg_KAB == cg_symmetric_key(server, _);
      }
  @*/
  //@ assert crypto_chars(?k, generated_key, KEY_SIZE, ccs_KAB);
  /*@ if (k == normal)
      {
        crypto_chars_to_chars(generated_key, KEY_SIZE);
        chars_to_secret_crypto_chars(generated_key, KEY_SIZE);
      }
  @*/
  //@ close cryptogram(generated_key, KEY_SIZE, ccs_KAB, cg_KAB);
  //@ assert cg_KAB == cg_symmetric_key(?p4, ?c4);
  //@ structure st = known_value(0, ccs_NB);
  //@ chars_split(msg + 16 + size1, 16);
  //@ assert chars(msg + 2 * 16 + size1, size2, ?msg_cs);
  //@ chars_to_crypto_chars(msg + 2 * 16 + size1, size2);
  //@ assert crypto_chars(normal, msg + 2 * 16 + size1, size2, ?msg_ccs);
  //@ close decryption_pre(true, false, receiver, st, msg_ccs);
  //@ chars_to_crypto_chars(msg + 16 + size1, 16);
  decrypt(generated_key, msg + 16 + size1, (unsigned int) size2, dec2);
  /*@ open decryption_post(true, ?garbage2, receiver,
                            st, p4, c4, _); @*/
  //@ open exists(?enc_cg2);
  //@ assert enc_cg2 == cg_aes_encrypted(?p3, ?c3, ?dec_ccs3, ?iv_ccs3);
  //@ open [_]yahalom_pub(enc_cg2);

  /*@ if (col || garbage2 || yahalom_public_key(p4, c4, true))
      {
        if (col || garbage2)
        {
          crypto_chars_to_chars(dec2, NONCE_SIZE);
          public_chars(dec2, NONCE_SIZE);
        }
        else
          public_crypto_chars(dec2, NONCE_SIZE);
        chars_to_crypto_chars(dec2, NONCE_SIZE);
        MEMCMP_PUB(dec2)
      }
      else
      {
        assert [_]yahalom_pub_msg4(?server2, ?sender2,
                                   ?receiver2, ?a_id2, ?NB2);
        MEMCMP_SEC(dec2, NB2)
      }
  @*/
  //@ open cryptogram(NB, NONCE_SIZE, ccs_NB, cg_NB);
  //@ MEMCMP_SEC(NB, cg_NB)
  if (crypto_memcmp(dec2, NB, NONCE_SIZE) != 0) abort();
  //@ close cryptogram(NB, NONCE_SIZE, ccs_NB, cg_NB);
  //@ assert crypto_chars(_, dec2, NONCE_SIZE, ccs_NB);
  /*@ if (garbage2)
      {
        close exists(pair(nil, nil));
        close has_structure(ccs_NB, st);
        leak has_structure(ccs_NB, st);
        decryption_garbage(dec2, NONCE_SIZE, st);
        crypto_chars_to_chars(dec2, NONCE_SIZE);
        chars_to_secret_crypto_chars(dec2, NONCE_SIZE);
      }
  @*/
  /*@ if (!col && !bad(server) && !bad(sender) && !bad(receiver))
      {
        assert [_]yahalom_pub_msg4(?server2, ?sender2,
                                    ?receiver2, ?a_id2, ?NB2);
        ccs_for_cg_inj(cg_NB, NB2);
        if (bad(server2) || bad(sender2) || bad(receiver2))
        {
          open [_]yahalom_pub(cg_NB);
          assert false;
        }
      }
  @*/
  //@ assert crypto_chars(?k1, dec2, NONCE_SIZE, ccs_NB);
  //@ if (k1 == normal) crypto_chars_to_chars(dec2, NONCE_SIZE);
  //@ if (k1 == normal) chars_to_secret_crypto_chars(dec2, NONCE_SIZE);
  //@ crypto_chars_to_chars(msg, 16 + size1);
  //@ crypto_chars_to_chars(msg + 16 + size1, 16 + size2);
  //@ chars_join(msg);
  free(msg);
  //@ assert crypto_chars(?k2, dec1 + ID_SIZE, KEY_SIZE, _);
  /*@ if(k2 == secret)
      {
        crypto_chars_to_chars(dec1, ID_SIZE);
        chars_to_secret_crypto_chars(dec1, ID_SIZE);
      }
  @*/
  //@ crypto_chars_join(dec1);
  zeroize(dec1, size1);
  free(dec1);
  zeroize(dec2, size2);
  free(dec2);
  //@ close principal(receiver, _);
}

void receiver(int server, int sender, int receiver,
              char *key, char *generated_key)
/*@ requires [_]public_invar(yahalom_pub) &*&
             [_]decryption_key_classifier(yahalom_public_key) &*&
             principal(receiver, ?r_id1) &*&
             [?f]cryptogram(key, KEY_SIZE, ?key_ccs, ?key_cg) &*&
               key_cg == cg_symmetric_key(receiver, ?r_id2) &*&
               cg_info(key_cg) == int_pair(3, server) &*&
             chars_(generated_key, KEY_SIZE, _); @*/
/*@ ensures  [_]public_invar(yahalom_pub) &*&
             principal(receiver, _) &*&
             [f]cryptogram(key, KEY_SIZE, key_ccs, key_cg) &*&
             cryptogram(generated_key, KEY_SIZE, _, ?g_key_cg) &*&
             col || bad(server) || bad(sender) || bad(receiver) ?
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
  //@ open principal(receiver, _);
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

  {
    // 1. A -> B. A, NA
    int size = ID_SIZE + NONCE_SIZE;
    char* message = malloc((size_t)size); if (message == 0) abort();
    if (net_recv(&socket_in, message, (unsigned int) size) != size)
      abort();
    //@ chars_split(message, ID_SIZE);
    //@ public_chars(message, ID_SIZE);
    //@ close check_identifier_ghost_args(true, false, 0, 0, 0, nil);
    //@ chars_to_crypto_chars(message, ID_SIZE);
    check_identifier(message, sender);
    //@ public_crypto_chars(message, ID_SIZE);
    //@ assert chars(message, ID_SIZE, ?msg_cs);
    //@ cs_to_ccs_inj(msg_cs, identifier(sender));
    //@ assert chars(message, ID_SIZE, identifier(sender));
    //@ assert chars(message + ID_SIZE, NONCE_SIZE, ?cs_NA);
    //@ public_chars(message + ID_SIZE, NONCE_SIZE);
    //@ chars_to_crypto_chars(message + ID_SIZE, NONCE_SIZE);
    crypto_memcpy(NA, (void*) message + ID_SIZE, NONCE_SIZE);
    //@ cs_to_ccs_crypto_chars(NA, cs_NA);
    //@ cs_to_ccs_crypto_chars(message + ID_SIZE, cs_NA);
    //@ chars_join(message);
    free(message);
  }

  //@ assert chars(NA, NONCE_SIZE, ?cs_NA);
  //@ chars_to_crypto_chars(NA, NONCE_SIZE);
  //@ assert crypto_chars(normal, NA, NONCE_SIZE, ?ccs_NA);
  //@ assert ccs_NA == cs_to_ccs(cs_NA);
  //@ cryptogram cg_NA = ccs_for_cg_sur(ccs_NA, tag_nonce);
  //@ assert cg_NA == cg_nonce(?s, ?s_id);
  //@ cs_to_ccs_crypto_chars(NA, cs_NA);
  //@ chars_to_secret_crypto_chars(NA, NONCE_SIZE);
  //@ public_ccs_cg(cg_NA);
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  /*@ close random_request(receiver, IP(2, IP(server,
                                      IP(sender, IP(s, s_id)))), false); @*/
  if (havege_random(&havege_state, NB, NONCE_SIZE) != 0) abort();
  //@ open cryptogram(NB, NONCE_SIZE, ?ccs_NB, ?cg_NB);

  /*@ if (bad(server) || bad(sender) || bad(receiver))
      {
        close cryptogram(NB, NONCE_SIZE, ccs_NB, cg_NB);
        close yahalom_pub(cg_NB);
        leak yahalom_pub(cg_NB);
        public_cryptogram(NB, cg_NB);
        public_chars(NB, NONCE_SIZE);
        assert [_]public_ccs(ccs_NB);
        chars_to_secret_crypto_chars(NB, NONCE_SIZE);
      }
  @*/

  {
    // 2. B -> S. B, ENC(KB, {A, NA, NB})
    int prefix_size = ID_SIZE + NONCE_SIZE;
    int p_size = prefix_size + NONCE_SIZE;
    char *plaintext = malloc((size_t)p_size); if (plaintext == 0) abort();
    int m_size = ID_SIZE + 16 + p_size;
    char *message = malloc((size_t)m_size); if (message == 0) abort();

    //@ list<crypto_char> sid_ccs = cs_to_ccs(identifier(sender));
    //@ list<crypto_char> rid_ccs = cs_to_ccs(identifier(receiver));
    write_identifier(message, receiver);
    //@ cs_to_ccs_crypto_chars(message, identifier(receiver));
    //@ assert chars(message, ID_SIZE, identifier(receiver));

    write_identifier(plaintext, sender);
    //@ cs_to_ccs_crypto_chars(plaintext, identifier(sender));
    //@ chars_to_secret_crypto_chars(plaintext, ID_SIZE);
    //@ assert crypto_chars(secret, plaintext, ID_SIZE, sid_ccs);

    crypto_memcpy((void*) plaintext + ID_SIZE, NA, NONCE_SIZE);
    crypto_memcpy((void*) plaintext + ID_SIZE + NONCE_SIZE, NB, NONCE_SIZE);
    //@ crypto_chars_join(plaintext);
    //@ crypto_chars_join(plaintext);
    //@ assert crypto_chars(secret, plaintext, p_size, ?p_ccs);
    //@ append_assoc(sid_ccs, ccs_NA, ccs_NB);
    //@ assert p_ccs == append(sid_ccs, append(ccs_NA, ccs_NB));
    //@ close principal(receiver, _);
    encrypt(&havege_state, key, plaintext,
            (unsigned int) p_size, (void*) message + ID_SIZE);
    //@ open cryptogram((void*) message + ID_SIZE + 16, p_size, ?enc_ccs, ?enc_cg);
    /*@ if (!col)
        {
          if (yahalom_public_key(receiver, r_id2, true))
          {
            take_append(ID_SIZE, sid_ccs, append(ccs_NA, ccs_NB));
            drop_append(ID_SIZE, sid_ccs, append(ccs_NA, ccs_NB));
            take_append(NONCE_SIZE, ccs_NA, ccs_NB);
            drop_append(NONCE_SIZE, ccs_NA, ccs_NB);
            crypto_chars_split(plaintext, ID_SIZE);
            crypto_chars_split(plaintext + ID_SIZE, NONCE_SIZE);
            public_crypto_chars(plaintext, ID_SIZE);
            public_crypto_chars((void*) plaintext + ID_SIZE, NONCE_SIZE);
            public_crypto_chars((void*) plaintext + ID_SIZE + NONCE_SIZE, NONCE_SIZE);

            assert chars(plaintext, ID_SIZE, ?cs_sid);
            assert chars((void*) plaintext + ID_SIZE, NONCE_SIZE, ?cs_NA0);
            cs_to_ccs_inj(cs_NA, cs_NA0);
            assert chars((void*) plaintext + ID_SIZE + NONCE_SIZE, NONCE_SIZE, ?cs_NB);
            cs_to_ccs_append(cs_NA, cs_NB);
            cs_to_ccs_append(cs_sid, append(cs_NA, cs_NB));

            chars_join(plaintext + ID_SIZE);
            chars_join(plaintext);
            public_chars(plaintext, p_size);
            chars_to_crypto_chars(plaintext, p_size);
          }
          else
          {
            close yahalom_pub_msg1(server, sender, cg_NA, cg_NB);
          }
          close yahalom_pub(enc_cg);
          leak yahalom_pub(enc_cg);
          close cryptogram((void*) message + ID_SIZE + 16, p_size, enc_ccs, enc_cg);
          public_cryptogram((void*) message + ID_SIZE + 16, enc_cg);
        }
        else
        {
          crypto_chars_to_chars(message + ID_SIZE + 16, p_size);
        }
    @*/
    //@ crypto_chars_to_chars(message + ID_SIZE, 16);
    //@ chars_join(message);
    //@ chars_join(message);
    //@ open principal(receiver, _);
    net_send(&socket_out, message, (unsigned int) m_size);
    zeroize(plaintext, p_size);
    free(plaintext);
    free(message);
  }
  //@ close principal(receiver, _);
  //@ close exists(cg_NA);
  //@ close cryptogram(NB, NONCE_SIZE, ccs_NB, cg_NB);
  receiver_(socket_in, sender, receiver, server, key,
            generated_key, NA, NB);
  //@ open cryptogram(NB, NONCE_SIZE, ccs_NB, cg_NB);

  //@ public_crypto_chars(NA, NONCE_SIZE);
  zeroize(NB, NONCE_SIZE);

  havege_free(&havege_state);
  //@ open havege_state(&havege_state);

  net_close(socket);
  net_close(socket_in);
  net_close(socket_out);
}

#endif
