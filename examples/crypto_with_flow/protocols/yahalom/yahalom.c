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
             [?f1]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
               key_cg == cg_symmetric_key(?principal2, ?id) &*&
             [?f2]crypto_chars(?kind, msg, msg_len, ?msg_cs) &*&
               1024 >= msg_len &*&
               msg_len >= MINIMAL_STRING_SIZE &*&
             chars(output, 16 + msg_len, _); @*/
/*@ ensures  havege_state_initialized(state) &*&
             principal(principal1, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_cs, key_cg) &*&
             [f2]crypto_chars(kind, msg, msg_len, msg_cs) &*&
             chars(output, 16, ?iv_cs) &*&
             cryptogram(output + 16, msg_len, _, ?enc_cg) &*&
             enc_cg == cg_encrypted(principal2, id, msg_cs, iv_cs); @*/
{
  //@ open principal(principal1, _);
  char iv[16];
  aes_context aes_context;
  unsigned int iv_off = 0;
  //@ chars_limits(output);

  //@ close random_request(principal1, IP(0, 0), false);
  if (havege_random(state, iv, 16) != 0) abort();
  //@ open cryptogram(iv, 16, ?iv_cs, ?iv_cg);
  //@ close yahalom_pub(iv_cg);
  //@ leak yahalom_pub(iv_cg);
  memcpy(output, iv, 16);
  //@ close cryptogram(output, 16, iv_cs, iv_cg);
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
  //@ assert cryptogram(output + 16, msg_len, ?enc_cs, ?enc_cg);
  //@ assert enc_cg == cg_encrypted(principal2, id, msg_cs, iv_cs);
  //@ close principal(principal1, _);
}

void decrypt(char *key, char *msg, unsigned int msg_len, char* output)
/*@ requires [_]public_invar(yahalom_pub) &*&
             decryption_pre(true, ?principal1, ?s,
                            initial_request, ?msg_cs) &*&
             random_permission(principal1, _) &*&
             [?f1]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
               key_cg == cg_symmetric_key(?principal2, ?id) &*&
             [?f2]chars(msg, 16, ?iv_cs) &*&
             [f2]chars(msg + 16, msg_len, msg_cs) &*&
               msg_len >= MINIMAL_STRING_SIZE &*& msg_len < 1024 &*&
             chars(output, msg_len, _); @*/
/*@ ensures  decryption_post(true, principal1, s, initial_request,
                             ?wrong_key, principal2, id, ?dec_cs) &*&
             random_permission(principal1, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_cs, key_cg) &*&
             [f2]chars(msg, 16 + msg_len, append(iv_cs, msg_cs)) &*&
             crypto_chars(?kind, output, msg_len, dec_cs) &*&
             exists(?enc_cg) &*& [_]yahalom_pub(enc_cg) &*&
             msg_cs == chars_for_cg(enc_cg) &*&
             enc_cg == cg_encrypted(?p, ?c, ?dec_cs2, ?iv_cs2) &*&
             wrong_key == (p != principal2 || c != id) &*&
             wrong_key ?
               kind == normal
             :
               kind == secret &*&
               p == principal2 &*& c == id &*&
               dec_cs == dec_cs2 && iv_cs == iv_cs2; @*/
{
  char iv[16];
  aes_context aes_context;
  unsigned int iv_off = 0;
  //@ chars_limits(msg);

  //@ cryptogram iv_cg = chars_for_cg_sur(iv_cs, tag_nonce);
  //@ public_chars(msg, 16);
  //@ public_chars_extract(msg, iv_cg);
  //@ chars_to_secret_crypto_chars(msg, 16);
  memcpy(iv, msg, 16);
  //@ public_crypto_chars(msg, 16);

  //@ close aes_context(&aes_context);
  if (aes_setkey_enc(&aes_context, key, (unsigned int) KEY_SIZE * 8) != 0)
    abort();
  //@ interpret_encrypted(msg + 16, msg_len);
  //@ open [f2]cryptogram(msg + 16, msg_len, msg_cs, ?enc_cg);
  //@ close [f2]cryptogram(msg + 16, msg_len, msg_cs, enc_cg);
  //@ assert enc_cg == cg_encrypted(?p, ?c, ?pay_cs2, ?iv_cs2);
  //@ open [_]yahalom_pub(enc_cg);
  //@ close exists(enc_cg);
  if (aes_crypt_cfb128(&aes_context, AES_DECRYPT,
                       (unsigned int) msg_len,
                       &iv_off, iv, msg + 16, output) != 0)
    abort();
  //@ public_cryptogram(msg + 16, enc_cg);
  zeroize(iv, 16);
  aes_free(&aes_context);
  //@ open aes_context(&aes_context);
  //@ chars_join(msg);
}

void decrypt_id(char *key, char *msg, unsigned int msg_len, char* output, int tag)
/*@ requires [_]public_invar(yahalom_pub) &*&
             [_]decryption_key_classifier(yahalom_public_key) &*&
             principal(?principal1, _) &*&
             [?f1]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
               key_cg == cg_symmetric_key(?principal2, ?id) &*&
             [?f2]chars(msg, 16, ?iv_cs) &*&
             [f2]chars(msg + 16, msg_len, ?msg_cs) &*&
               msg_len >= ID_SIZE &*& msg_len < 1024 &*&
             chars(output, msg_len, _); @*/
/*@ ensures  principal(principal1, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_cs, key_cg) &*&
             [f2]chars(msg, 16 + msg_len, append(iv_cs, msg_cs)) &*&
             crypto_chars(?kind, output, msg_len, ?dec_cs) &*&
             take(ID_SIZE, dec_cs) == identifier(tag) &*&
             [_]public_generated(yahalom_pub)(take(ID_SIZE, dec_cs)) &*&
             exists(?enc_cg) &*&
             enc_cg == cg_encrypted(?p, ?c, ?dec_cs2, ?iv_cs2) &*&
             [_]yahalom_pub(enc_cg) &*&
             col || yahalom_public_key(principal2, id, true) ?
               kind == normal
             :
               kind == secret &*&
               msg_cs == chars_for_cg(enc_cg) &*&
               p == principal2 &*& c == id &*&
               dec_cs == dec_cs2 && iv_cs == iv_cs2; @*/
{
  //@ structure s = known_value(0, identifier(tag));
  //@ close decryption_pre(true, principal1, s, initial_request, msg_cs);
  decrypt(key, msg, msg_len, output);
  //@ open [_]yahalom_pub(?enc_cg);
  /*@ open decryption_post(true, principal1, s, initial_request,
                           ?wrong_key, principal2, id, ?dec_cs); @*/
  //@ if (col || wrong_key) public_chars(output, msg_len);
  //@ if (col || wrong_key) chars_to_crypto_chars(output, msg_len);
  //@ close check_identifier_ghost_args(true, wrong_key, principal2, id);
  check_identifier(output, tag);
  //@ assert crypto_chars(secret, output, msg_len, dec_cs);
  //@ close principal(principal1, _);
  /*@ if (col || yahalom_public_key(principal2, id, true))
      {
        public_crypto_chars(output, msg_len);
        chars_to_crypto_chars(output, msg_len);
      }
  @*/
}

#ifdef INCLUDE_SERVER

void server(int server, int sender, int receiver,
            char *s_key, char *r_key)
/*@ requires [_]public_invar(yahalom_pub) &*&
             [_]decryption_key_classifier(yahalom_public_key) &*&
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
    char *decrypted = malloc(d_size); if (decrypted == 0) abort();
    int m_size = ID_SIZE + 16 + d_size;
    char *message = malloc(m_size); if (message == 0) abort();

    // Receive the message
    net_recv(&socket_in, message, (unsigned int) m_size);
    //@ chars_split(message, ID_SIZE);
    //@ chars_split(message + ID_SIZE, 16);
    //@ chars_to_crypto_chars(message, ID_SIZE);
    //@ close check_identifier_ghost_args(true, false, 0, 0);
    check_identifier(message, receiver);
    //@ public_crypto_chars(message, ID_SIZE);
    //@ assert chars(message, ID_SIZE, identifier(receiver));
    //@ assert chars(message + ID_SIZE, 16, ?iv_cs);
    //@ assert chars(message + ID_SIZE + 16, d_size, ?enc_cs);
    //@ close principal(server, _);
    decrypt_id(r_key, (void*) message + ID_SIZE, (unsigned int) d_size,
               decrypted, sender);
    //@ open principal(server, _);
    //@ crypto_chars_split(decrypted, ID_SIZE);
    //@ crypto_chars_split((void*) decrypted + ID_SIZE, NONCE_SIZE);
    memcpy(NA, (void*) decrypted + ID_SIZE, NONCE_SIZE);
    memcpy(NB, (void*) decrypted + prefix_size, NONCE_SIZE);
    //@ assert crypto_chars(?kind, decrypted + ID_SIZE, NONCE_SIZE, ?NA_cs);
    /*@ assert crypto_chars(kind, (void*) decrypted + ID_SIZE + NONCE_SIZE,
                                   NONCE_SIZE, ?NB_cs); @*/
    //@ NA_cg = chars_for_cg_sur(NA_cs, tag_nonce);
    //@ NB_cg = chars_for_cg_sur(NB_cs, tag_nonce);
    //@ crypto_chars_join((void*) decrypted + ID_SIZE);
    //@ crypto_chars_join(decrypted);

    //@ open [_]yahalom_pub(?enc_cg);
    //@ condition = col || yahalom_public_key(receiver, r_id, true);
    /*@ if (condition)
        {
          crypto_chars_to_chars(decrypted, d_size);
          chars_split(decrypted, ID_SIZE);
          chars_split((void*) decrypted + ID_SIZE, NONCE_SIZE);
          public_chars((void*) decrypted + ID_SIZE, NONCE_SIZE);
          public_crypto_chars_extract(NA, NA_cg);
          public_chars((void*) decrypted + ID_SIZE + NONCE_SIZE, NONCE_SIZE);
          public_crypto_chars_extract(NB, NB_cg);
          chars_join((void*) decrypted + ID_SIZE);
          chars_join(decrypted);
          chars_to_crypto_chars(decrypted, d_size);
        }
        else
        {
          assert [_]yahalom_pub_msg1(?srv2, ?s2, ?NA2, ?NB2);
          take_append(ID_SIZE, identifier(sender), append(NA_cs, NB_cs));
          take_append(ID_SIZE, identifier(s2),
                                append(chars_for_cg(NA2), chars_for_cg(NB2)));
          drop_append(ID_SIZE, identifier(sender), append(NA_cs, NB_cs));
          drop_append(ID_SIZE, identifier(s2),
                                append(chars_for_cg(NA2), chars_for_cg(NB2)));
          take_append(NONCE_SIZE, NA_cs, NB_cs);
          take_append(NONCE_SIZE, chars_for_cg(NA2), chars_for_cg(NB2));
          drop_append(NONCE_SIZE, NA_cs, NB_cs);
          drop_append(NONCE_SIZE, chars_for_cg(NA2), chars_for_cg(NB2));
          assert srv2 == server;
          equal_identifiers(s2, sender);
          assert s2 == sender;
          assert chars_for_cg(NA2) == NA_cs;
          NA_cg = NA2;
          close cryptogram(NA, NONCE_SIZE, NA_cs, NA_cg);
          public_cryptogram(NA, NA_cg);
          assert chars_for_cg(NB2) == NB_cs;
          NB_cg = NB2;
          assert NB_cg == cg_nonce(receiver, _);
        }
    @*/
    zeroize(decrypted, d_size);
    free(decrypted);
    //@ chars_join(message);
    free(message);
  }

  //@ assert chars(NA, NONCE_SIZE, ?cs_NA);
  //@ public_chars(NA, NONCE_SIZE);
  //@ assert cs_NA == chars_for_cg(NA_cg);
  //@ assert NA_cg == cg_nonce(?s2, ?a_id);
  //@ assert crypto_chars(secret, NB, NONCE_SIZE, ?cs_NB);
  //@ assert cs_NB == chars_for_cg(NB_cg);
  //@ assert NB_cg == cg_nonce(?r2, ?b_id);

  /*@ close random_request(server, IP(4, IP(sender, IP(receiver,
                                   IP(s2, IP(a_id, IP(r2, b_id)))))), true); @*/

  if (havege_random(&havege_state, KAB, KEY_SIZE) != 0) abort();
  //@ open cryptogram(KAB, KEY_SIZE, ?cs_KAB, ?cg_KAB);
  //@ assert cg_KAB == cg_symmetric_key(server, ?id_KAB);
  /*@ if (yahalom_public_key(server, id_KAB, true))
      {
        close cryptogram(KAB, KEY_SIZE, cs_KAB, cg_KAB);
        close yahalom_pub(cg_KAB);
        leak yahalom_pub(cg_KAB);
        public_cryptogram(KAB, cg_KAB);
        public_chars(KAB, KEY_SIZE);
        chars_to_secret_crypto_chars(KAB, KEY_SIZE);
        assert [_]public_generated(yahalom_pub)(cs_KAB);
      }
  @*/

  {
    // 3. S -> A. ENC(KA, {B, KAB, NA, NB}), ENC(KB, {A, KAB})
    int size1 = 16 + ID_SIZE + KEY_SIZE + NONCE_SIZE + NONCE_SIZE;
    int size2 = 16 + ID_SIZE + KEY_SIZE;
    char *enc1 = malloc(size1); if (enc1 == 0) abort();
    char *enc2 = malloc(size2); if (enc2 == 0) abort();
    {
      //ENC(KA, {B, KAB, NA, NB})
      int s = ID_SIZE + KEY_SIZE + NONCE_SIZE + NONCE_SIZE;
      char* m = malloc(s); if (m == 0) abort();
      write_identifier(m, receiver);
      //@ chars_to_secret_crypto_chars(m, ID_SIZE);
      //@ assert crypto_chars(secret, m, ID_SIZE, identifier(receiver));
      memcpy(m + ID_SIZE, KAB, KEY_SIZE);
      //@ chars_to_secret_crypto_chars(NA, NONCE_SIZE);
      memcpy(m + ID_SIZE + KEY_SIZE, NA, NONCE_SIZE);
      //@ public_crypto_chars(NA, NONCE_SIZE);
      /*@ if (col || yahalom_public_key(receiver, r_id, true))
            chars_to_secret_crypto_chars(NB, NONCE_SIZE); @*/
      memcpy(m + ID_SIZE + KEY_SIZE + NONCE_SIZE, NB, NONCE_SIZE);
      //@ crypto_chars_join(m + ID_SIZE + KEY_SIZE);
      //@ crypto_chars_join(m + ID_SIZE);
      //@ crypto_chars_join(m);
      //@ close principal(server, _);
      encrypt(&havege_state, s_key, m,
              (unsigned int) (ID_SIZE + KEY_SIZE + NONCE_SIZE + NONCE_SIZE), enc1);
      //@ open cryptogram(enc1 + 16, s, ?enc_cs, ?enc_cg);
      /*@ if (!col)
          {
            list <char> dec_cs = append(identifier(receiver),
                                 append(cs_KAB, append(cs_NA, cs_NB)));
            assert enc_cg == cg_encrypted(sender, s_id, dec_cs, ?ent);

            if (yahalom_public_key(sender, s_id, true))
            {
              assert true == yahalom_public_key(server, id_KAB, true);
              take_append(ID_SIZE, identifier(receiver),
                          append(cs_KAB, append(cs_NA, cs_NB)));
              drop_append(ID_SIZE, identifier(receiver),
                          append(cs_KAB, append(cs_NA, cs_NB)));
              take_append(KEY_SIZE, cs_KAB, append(cs_NA, cs_NB));
              drop_append(KEY_SIZE, cs_KAB, append(cs_NA, cs_NB));
              take_append(NONCE_SIZE, cs_NA, cs_NB);
              crypto_chars_split(m, ID_SIZE);
              crypto_chars_split(m + ID_SIZE, KEY_SIZE);
              crypto_chars_split(m + ID_SIZE + KEY_SIZE, NONCE_SIZE);
              public_crypto_chars(m, ID_SIZE);
              close yahalom_pub(cg_KAB);
              leak yahalom_pub(cg_KAB);
              close cryptogram(m + ID_SIZE, KEY_SIZE, cs_KAB, cg_KAB);
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
                                 NONCE_SIZE, cs_NB, NB_cg);
                public_cryptogram(m + ID_SIZE + KEY_SIZE + NONCE_SIZE, NB_cg);
              }
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
                             enc_cs, enc_cg);
            public_cryptogram(enc1 + 16, enc_cg);
            chars_join(enc1);
            public_chars(enc1, s + 16);
            chars_to_crypto_chars(enc1, s + 16);
          }
          else
          {
            crypto_chars_to_chars(enc1 + 16, s);
            chars_join(enc1);
            public_chars(enc1, s + 16);
            chars_to_crypto_chars(enc1, s + 16);
          }
      @*/
      zeroize(m, ID_SIZE + KEY_SIZE + NONCE_SIZE + NONCE_SIZE);
      free(m);
    }

    {
      //ENC(KB, {A, KAB})
      int s = ID_SIZE + KEY_SIZE;
      char* m = malloc(s); if (m == 0) abort();
      write_identifier(m, sender);
      //@ chars_to_secret_crypto_chars(m, ID_SIZE);
      //@ assert crypto_chars(secret, m, ID_SIZE, identifier(sender));
      memcpy(m + ID_SIZE, KAB, KEY_SIZE);
      //@ crypto_chars_join(m);

      encrypt(&havege_state, r_key, m, (unsigned int) (ID_SIZE + KEY_SIZE), enc2);
      //@ open cryptogram(enc2 + 16, ID_SIZE + KEY_SIZE, ?enc_cs, ?enc_cg);
      /*@ if (!col)
          {
            assert enc_cg == cg_encrypted(receiver, r_id,
                                append(identifier(sender), cs_KAB), ?ent);
            if (yahalom_public_key(receiver, r_id, true))
            {
              assert true == yahalom_public_key(server, id_KAB, true);
              take_append(ID_SIZE, identifier(sender), cs_KAB);
              drop_append(ID_SIZE, identifier(sender), cs_KAB);
              crypto_chars_split(m, ID_SIZE);
              public_crypto_chars(m, ID_SIZE);
              close cryptogram(m + ID_SIZE, KEY_SIZE, cs_KAB, cg_KAB);
              close yahalom_pub(cg_KAB);
              leak yahalom_pub(cg_KAB);
              public_cryptogram(m + ID_SIZE, cg_KAB);
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
            close cryptogram(enc2 + 16, ID_SIZE + KEY_SIZE, enc_cs, enc_cg);
            public_cryptogram(enc2 + 16, enc_cg);
            chars_join(enc2);
            public_chars(enc2, s + 16);
            chars_to_crypto_chars(enc2, s + 16);
          }
          else
          {
            crypto_chars_to_chars(enc2 + 16, s);
            chars_join(enc2);
            public_chars(enc2, s + 16);
            chars_to_crypto_chars(enc2, s + 16);
          }
      @*/
      zeroize(m, ID_SIZE + KEY_SIZE);
      free(m);
    }

    {
      int size = size1 + size2;
      char *message = malloc(size); if (message == 0) abort();
      memcpy(message, enc1, (unsigned int) size1);
      memcpy(message + size1, enc2, (unsigned int) size2);
      //@ crypto_chars_join(message);
      //@ crypto_chars_to_chars(message, size);
      //@ open principal(server, _);
      net_send(&socket_out, message, (unsigned int) size);

      free(message);
    }

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
             [?f]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
               key_cg == cg_symmetric_key(sender, ?s_id2) &*&
               cg_info(key_cg) == IP(3, server) &*&
             chars(generated_key, KEY_SIZE, _); @*/
/*@ ensures  principal(sender, _) &*&
             [f]cryptogram(key, KEY_SIZE, key_cs, key_cg) &*&
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

  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  //@ close random_request(sender, int_pair(1, int_pair(sender, receiver)), false);
  if (havege_random(&havege_state, NA, NONCE_SIZE) != 0) abort();
  //@ open cryptogram(NA, NONCE_SIZE, ?cs_NA, ?cg_NA);
  //@ close cryptogram(NA, NONCE_SIZE, cs_NA, cg_NA);
  //@ assert cg_NA == cg_nonce(sender, s_id + 1);
  //@ close yahalom_pub(cg_NA);
  //@ leak yahalom_pub(cg_NA);
  //@ public_cryptogram(NA, cg_NA);
  //@ public_chars(NA, NONCE_SIZE);
  //@ chars_to_crypto_chars(NA, NONCE_SIZE);

  {
    // 1. A -> B. A, NA
    char* message = malloc(ID_SIZE + NONCE_SIZE); if (message == 0) abort();

    write_identifier(message, sender);
    //@ crypto_chars_split(message, ID_SIZE);
    memcpy((void*) message + ID_SIZE, NA, NONCE_SIZE);
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
    char *msg = malloc(size); if (msg == 0) abort();
    char *dec = malloc(size1); if (dec == 0) abort();
    MB = malloc(size2); if (MB == 0) abort();

    net_recv(&socket_in, msg, (unsigned int) size);
    //@ chars_split(msg, 16 + size1);
    //@ chars_to_crypto_chars(msg + 16 + size1, size2);
    memcpy(MB, msg + 16 + size1, (unsigned int) size2);
    //@ close principal(sender, _);
    decrypt_id(key, (void*) msg, (unsigned int) size1, dec, receiver);
    //@ open principal(sender, _);
    //@ crypto_chars_to_chars(msg + 16 + size1, size2);
    //@ chars_join(msg);
    free(msg);
    //@ assert crypto_chars(?kind, dec, size1, ?dec_cs);
    //@ bool condition = col || yahalom_public_key(sender, s_id2, true);
    //@ if (condition) public_chars(dec, size1);
    //@ if (condition) chars_to_crypto_chars(dec, size1);
    //@ assert exists(?enc_cg);
    //@ assert enc_cg == cg_encrypted(?p2, ?c2, ?dec_cs2, ?iv_cs2);
    //@ crypto_chars_split(dec, ID_SIZE);
    //@ crypto_chars_split(dec + ID_SIZE, KEY_SIZE);
    //@ crypto_chars_split(dec + ID_SIZE + KEY_SIZE, NONCE_SIZE);

    //@ assert crypto_chars(kind, dec, ID_SIZE, identifier(receiver));
    memcpy(generated_key, (void*) dec + ID_SIZE, KEY_SIZE);
    //@ assert crypto_chars(kind, generated_key, KEY_SIZE, ?cs_KAB);
    if (memcmp(NA, dec + ID_SIZE + KEY_SIZE, NONCE_SIZE) != 0) abort();
    //@ public_crypto_chars(dec + ID_SIZE + KEY_SIZE, NONCE_SIZE);
    /*@ if (kind == secret)
          chars_to_secret_crypto_chars(dec + ID_SIZE + KEY_SIZE, NONCE_SIZE);
        else
          chars_to_crypto_chars(dec + ID_SIZE + KEY_SIZE, NONCE_SIZE);
    @*/
    memcpy(NB, (void*) dec + ID_SIZE + KEY_SIZE + NONCE_SIZE, NONCE_SIZE);
    //@ assert crypto_chars(kind, NB, NONCE_SIZE, ?cs_NB);
    /*@ assert dec_cs == append(identifier(receiver), append(cs_KAB,
                                append(cs_NA, cs_NB))); @*/

    //@ open [_]yahalom_pub(enc_cg);
    //@ cg_NB = chars_for_cg_sur(cs_NB, tag_nonce);
    //@ cg_KAB = chars_for_cg_sur(cs_KAB, tag_symmetric_key);
    /*@ if (condition)
        {
          if (!col)
          {
            public_generated_split(yahalom_pub, dec_cs, ID_SIZE);
            public_generated_split(yahalom_pub,
              append(cs_KAB, append(cs_NA, cs_NB)), KEY_SIZE);
            public_generated_split(yahalom_pub,
              append(cs_NA, cs_NB), NONCE_SIZE);
            public_crypto_chars(NB, NONCE_SIZE);
            public_chars_extract(NB, cg_NB);
            chars_to_secret_crypto_chars(NB, NONCE_SIZE);
            public_crypto_chars(generated_key, KEY_SIZE);
            public_chars_extract(generated_key, cg_KAB);
            chars_to_secret_crypto_chars(generated_key, KEY_SIZE);
          }
          else
          {
            crypto_chars_to_chars(generated_key, KEY_SIZE);
            public_chars_extract(generated_key, cg_KAB);
            chars_to_secret_crypto_chars(generated_key, KEY_SIZE);
            crypto_chars_to_chars(NB, NONCE_SIZE);
            public_chars_extract(NB, cg_NB);
            chars_to_secret_crypto_chars(NB, NONCE_SIZE);
          }
        }
        else
        {
          assert [_]yahalom_pub_msg2(?server2, ?receiver2, ?NA2, ?NB2,
                                     ?KAB2);
          assert length(identifier(receiver2)) == ID_SIZE;
          take_append(ID_SIZE, identifier(receiver2), append(chars_for_cg(KAB2),
                      append(chars_for_cg(NA2), chars_for_cg(NB2))));
          drop_append(ID_SIZE, identifier(receiver2), append(chars_for_cg(KAB2),
                      append(chars_for_cg(NA2), chars_for_cg(NB2))));
          take_append(ID_SIZE, identifier(receiver), append(cs_KAB,
                      append(cs_NA, cs_NB)));
          drop_append(ID_SIZE, identifier(receiver), append(cs_KAB,
                      append(cs_NA, cs_NB)));
          assert identifier(receiver2) == identifier(receiver);
          take_append(KEY_SIZE, chars_for_cg(KAB2),
                      append(chars_for_cg(NA2), chars_for_cg(NB2)));
          drop_append(KEY_SIZE, chars_for_cg(KAB2),
                      append(chars_for_cg(NA2), chars_for_cg(NB2)));
          take_append(KEY_SIZE, cs_KAB, append(cs_NA, cs_NB));
          drop_append(KEY_SIZE, cs_KAB, append(cs_NA, cs_NB));
          assert cs_KAB == chars_for_cg(KAB2);
          take_append(NONCE_SIZE, chars_for_cg(NA2), chars_for_cg(NB2));
          drop_append(NONCE_SIZE, chars_for_cg(NA2), chars_for_cg(NB2));
          take_append(NONCE_SIZE, cs_NA, cs_NB);
          drop_append(NONCE_SIZE, cs_NA, cs_NB);
          assert cs_NA == chars_for_cg(NA2);
          equal_identifiers(receiver2, receiver);
          assert receiver2 == receiver;
          cg_KAB = KAB2;
          assert cg_KAB == cg_symmetric_key(server, _);
          chars_for_cg_inj(cg_NA, NA2);
          assert cg_NA == cg_nonce(?s, ?a_id);
          assert NB2 == cg_nonce(?r, ?b_id);
          cg_NB = NB2;
          chars_for_cg_inj(cg_NB, NB2);
          assert chars_for_cg(cg_NB) == cs_NB;
          assert server2 == server;
          assert cg_info(cg_KAB) == IP(4, IP(sender, IP(receiver,
                                      IP(s, IP(a_id, IP(r, b_id))))));
        }
    @*/
    //@ close cryptogram(generated_key, KEY_SIZE, cs_KAB, cg_KAB);
    //@ crypto_chars_join(dec + ID_SIZE + KEY_SIZE);
    //@ crypto_chars_join(dec + ID_SIZE);
    //@ crypto_chars_join(dec);
    zeroize(dec, size1);
    free(dec);
  }

  //@ assert crypto_chars(secret, NB, NONCE_SIZE, ?cs_NB);
  //@ assert cs_NB == chars_for_cg(cg_NB);
  //@ open cryptogram(generated_key, KEY_SIZE, ?cs_KAB, cg_KAB);
  //@ close cryptogram(generated_key, KEY_SIZE, cs_KAB, cg_KAB);

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
    char *enc2 = malloc(size2); if (enc2 == 0) abort();
    {
      //@ close principal(sender, _);
      encrypt(&havege_state, generated_key, NB, NONCE_SIZE, enc2);
      //@ open cryptogram(enc2 + 16, NONCE_SIZE, ?enc_cs, ?enc_cg);
      /*@ if (!col)
          {
            if (yahalom_public_key(p0, c0, true))
            {
              if (!bad(server) && !bad(sender) && bad(receiver))
              {
                assert [_]yahalom_pub(cg_NB);
                close cryptogram(NB, NONCE_SIZE, cs_NB, cg_NB);
                public_cryptogram(NB, cg_NB);
                public_chars(NB, NONCE_SIZE);
                chars_to_crypto_chars(NB, NONCE_SIZE);
              }
            }
            else
            {
              if (bad(server) || bad(sender) || bad(server))
              {
                public_crypto_chars_extract(NB, cg_NB);
                chars_to_crypto_chars(NB, NONCE_SIZE);
              }
              close yahalom_pub_msg4(server, sender, receiver, a_id, cg_NB);
            }
            close yahalom_pub(enc_cg);
            leak yahalom_pub(enc_cg);
            close cryptogram(enc2 + 16, NONCE_SIZE, enc_cs, enc_cg);
            public_cryptogram(enc2 + 16, enc_cg);
          }
          else
          {
            crypto_chars_to_chars(enc2 + 16, NONCE_SIZE);
          }
      @*/
      //@ chars_join(enc2);
      //@ chars_to_crypto_chars(enc2, size2);
    }

    {
      int size = size1 + size2;
      char *message = malloc(size); if (message == 0) abort();
      memcpy(message, MB, (unsigned int) size1);
      memcpy(message + size1, enc2, (unsigned int) size2);
      //@ crypto_chars_join(message);
      //@ crypto_chars_to_chars(message, size);
      //@ open principal(sender, _);
      net_send(&socket_out, message, (unsigned int) size);
      free(message);
    }

    free(enc2);
  }

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

void receiver(int server, int sender, int receiver,
              char *key, char *generated_key)
/*@ requires [_]public_invar(yahalom_pub) &*&
             [_]decryption_key_classifier(yahalom_public_key) &*&
             principal(receiver, ?r_id1) &*&
             [?f]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
               key_cg == cg_symmetric_key(receiver, ?r_id2) &*&
               cg_info(key_cg) == int_pair(3, server) &*&
             chars(generated_key, KEY_SIZE, _); @*/
/*@ ensures  [_]public_invar(yahalom_pub) &*&
             principal(receiver, _) &*&
             [f]cryptogram(key, KEY_SIZE, key_cs, key_cg) &*&
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
    char* message = malloc(size); if (message == 0) abort();
    net_recv(&socket_in, message, (unsigned int) size);
    //@ chars_to_crypto_chars(message, ID_SIZE + NONCE_SIZE);
    //@ crypto_chars_split(message, ID_SIZE);
    //@ close check_identifier_ghost_args(true, false, 0, 0);
    check_identifier(message, sender);
    //@ public_crypto_chars(message, ID_SIZE);
    //@ assert chars(message, ID_SIZE, identifier(sender));
    //@ assert chars(message + ID_SIZE, NONCE_SIZE, ?cs_NA);
    memcpy(NA, (void*) message + ID_SIZE, NONCE_SIZE);
    //@ public_chars(message + ID_SIZE, NONCE_SIZE);
    //@ crypto_chars_to_chars(NA, NONCE_SIZE);
    //@ chars_join(message);
    free(message);
  }

  //@ assert chars(NA, NONCE_SIZE, ?cs_NA);
  //@ cryptogram cg_NA = chars_for_cg_sur(cs_NA, tag_nonce);
  //@ assert cg_NA == cg_nonce(?s, ?s_id);
  //@ public_chars_extract(NA, cg_NA);
  //@ chars_to_secret_crypto_chars(NA, NONCE_SIZE);
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  /*@ close random_request(receiver, IP(2, IP(server,
                                      IP(sender, IP(s, s_id)))), false); @*/
  if (havege_random(&havege_state, NB, NONCE_SIZE) != 0) abort();
  //@ open cryptogram(NB, NONCE_SIZE, ?cs_NB, ?cg_NB);

  /*@ if (bad(server) || bad(sender) || bad(receiver))
      {
        close cryptogram(NB, NONCE_SIZE, cs_NB, cg_NB);
        close yahalom_pub(cg_NB);
        leak yahalom_pub(cg_NB);
        public_cryptogram(NB, cg_NB);
        public_chars(NB, NONCE_SIZE);
        assert [_]public_generated(yahalom_pub)(cs_NB);
        chars_to_secret_crypto_chars(NB, NONCE_SIZE);
      }
  @*/

  {
    // 2. B -> S. B, ENC(KB, {A, NA, NB})
    int prefix_size = ID_SIZE + NONCE_SIZE;
    int p_size = prefix_size + NONCE_SIZE;
    char *plaintext = malloc(p_size); if (plaintext == 0) abort();
    int m_size = ID_SIZE + 16 + p_size;
    char *message = malloc(m_size); if (message == 0) abort();

    write_identifier(message, receiver);
    //@ crypto_chars_split(message, ID_SIZE);
    //@ crypto_chars_to_chars(message, ID_SIZE);
    //@ assert chars(message, ID_SIZE, identifier(receiver));

    write_identifier(plaintext, sender);
    //@ crypto_chars_split(plaintext, ID_SIZE);
    //@ crypto_chars_to_chars(plaintext, ID_SIZE);
    //@ chars_to_secret_crypto_chars(plaintext, ID_SIZE);
    //@ assert crypto_chars(secret, plaintext, ID_SIZE, identifier(sender));
    memcpy((void*) plaintext + ID_SIZE, NA, NONCE_SIZE);
    memcpy((void*) plaintext + ID_SIZE + NONCE_SIZE, NB, NONCE_SIZE);
    //@ crypto_chars_join(plaintext);
    //@ crypto_chars_join(plaintext);
    //@ assert crypto_chars(secret, plaintext, p_size, ?p_cs);
    //@ append_assoc(identifier(sender), cs_NA, cs_NB);
    //@ assert p_cs == append(identifier(sender), append(cs_NA, cs_NB));
    //@ close principal(receiver, _);
    encrypt(&havege_state, key, plaintext,
            (unsigned int) p_size, (void*) message + ID_SIZE);
    //@ open cryptogram((void*) message + ID_SIZE + 16, p_size, ?enc_cs, ?enc_cg);
    /*@ if (!col)
        {
          if (yahalom_public_key(receiver, r_id2, true))
          {
            take_append(ID_SIZE, identifier(sender), append(cs_NA, cs_NB));
            drop_append(ID_SIZE, identifier(sender), append(cs_NA, cs_NB));
            take_append(NONCE_SIZE, cs_NA, cs_NB);
            drop_append(NONCE_SIZE, cs_NA, cs_NB);
            crypto_chars_split(plaintext, ID_SIZE);
            crypto_chars_split(plaintext + ID_SIZE, NONCE_SIZE);
            public_crypto_chars(plaintext, ID_SIZE);
            public_crypto_chars((void*) plaintext + ID_SIZE, NONCE_SIZE);
            public_crypto_chars((void*) plaintext + ID_SIZE + NONCE_SIZE, NONCE_SIZE);
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
          close cryptogram((void*) message + ID_SIZE + 16, p_size, enc_cs, enc_cg);
          public_cryptogram((void*) message + ID_SIZE + 16, enc_cg);
        }
        else
        {
          crypto_chars_to_chars(message + ID_SIZE + 16, p_size);
        }
    @*/
    //@ chars_join(message);
    //@ chars_join(message);
    //@ open principal(receiver, _);
    net_send(&socket_out, message, (unsigned int) m_size);
    zeroize(plaintext, p_size);
    free(message);
    free(plaintext);
    //@ crypto_chars_to_chars(message + ID_SIZE, 0);
    //@ crypto_chars_to_chars(plaintext + ID_SIZE, 0);
  }

  {
    // 4. A -> B. ENC(KB, {A, KAB}), ENC(KAB, NB)
    int size1 = ID_SIZE + KEY_SIZE;
    int size2 = NONCE_SIZE;
    int size = 16 + size1 + 16 + size2;
    char *msg = malloc(size); if (msg == 0) abort();
    char *dec1 = malloc(size1); if (dec1 == 0) abort();
    char *dec2 = malloc(size2); if (dec2 == 0) abort();
    net_recv(&socket_in, msg, (unsigned int) size);
    //@ close principal(receiver, _);
    //@ chars_split(msg, 16);
    //@ chars_split(msg + 16, size1);
    decrypt_id(key, (void*) msg, (unsigned int) size1, dec1, sender);
    //@ open principal(receiver, _);
    //@ open exists(?enc_cg);
    //@ assert enc_cg == cg_encrypted(?p, ?c, ?dec_cs2, ?iv_cs2);
    //@ open [_]yahalom_pub(enc_cg);
    //@ assert crypto_chars(?kind, dec1, size1, ?cs_dec1);
    //@ crypto_chars_split(dec1, ID_SIZE);
    memcpy(generated_key, dec1 + ID_SIZE, KEY_SIZE);
    //@ assert crypto_chars(kind, generated_key, KEY_SIZE, ?cs_KAB);
    //@ cg_KAB = chars_for_cg_sur(cs_KAB, tag_symmetric_key);
    /*@ if(col || yahalom_public_key(receiver, r_id2, true))
        {
          public_chars(generated_key, KEY_SIZE);
          crypto_chars_join(dec1);
          public_chars_extract(generated_key, cg_KAB);
        }
        else
        {
          crypto_chars_join(dec1);
          assert [_]yahalom_pub_msg3(?server2, ?sender2, ?KAB2, ?s2,
                                      ?a_id2, ?r2, ?b_id2);
          take_append(ID_SIZE, identifier(sender), cs_KAB);
          take_append(ID_SIZE, identifier(sender2), chars_for_cg(KAB2));
          drop_append(ID_SIZE, identifier(sender), cs_KAB);
          drop_append(ID_SIZE, identifier(sender2), chars_for_cg(KAB2));
          assert server2 == server;
          equal_identifiers(sender2, sender);
          assert sender2 == sender;
          cg_KAB = KAB2;
          assert cg_KAB == cg_symmetric_key(server, _);
        }
    @*/
    //@ close cryptogram(generated_key, KEY_SIZE, cs_KAB, cg_KAB);
    //@ assert cg_KAB == cg_symmetric_key(?p4, ?c4);
    //@ structure st = known_value(0, cs_NB);
    //@ chars_split(msg + 16 + size1, 16);
    //@ assert chars(msg + 2 * 16 + size1, size2, ?msg_cs);
    /*@ close decryption_pre(true, receiver, st,
                                 initial_request, msg_cs); @*/
    decrypt(generated_key, msg + 16 + size1, (unsigned int) size2, dec2);
    /*@ open decryption_post(true, receiver, st, initial_request,
                                 ?wrong_key, p4, c4, _); @*/
    //@ open exists(?enc_cg2);
    //@ assert enc_cg2 == cg_encrypted(?p3, ?c3, ?dec_cs3, ?iv_cs3);
    //@ open [_]yahalom_pub(enc_cg2);
    if (memcmp(dec2, NB, NONCE_SIZE) != 0) abort();
    //@ assert crypto_chars(_, dec2, NONCE_SIZE, cs_NB);

    /*@ if (wrong_key)
        {
          close exists(pair(nil, nil));
          close has_structure(cs_NB, st);
          leak has_structure(cs_NB, st);
          decryption_with_wrong_key(dec2, NONCE_SIZE, st);
          chars_to_secret_crypto_chars(dec2, NONCE_SIZE);
        }
    @*/
    //@ assert crypto_chars(secret, dec2, NONCE_SIZE, cs_NB);
    /*@ if (!col && !bad(server) && !bad(sender) && !bad(receiver))
        {
          assert [_]yahalom_pub_msg4(?server2, ?sender2,
                                     ?receiver2, ?a_id2, ?NB2);
          assert NB2 == cg_nonce(?b2, ?b_id2);
          chars_for_cg_inj(cg_NB, NB2);
          if (bad(server2) || bad(sender2) || bad(receiver2))
          {
            open [_]yahalom_pub(cg_NB);
            assert false;
          }
        }
    @*/

    free(msg);
    zeroize(dec1, size1);
    free(dec1);
    zeroize(dec2, size2);
    free(dec2);
  }

  //@ public_crypto_chars(NA, NONCE_SIZE);
  zeroize(NB, NONCE_SIZE);

  havege_free(&havege_state);
  //@ open havege_state(&havege_state);

  net_close(socket);
  net_close(socket_in);
  net_close(socket_out);
  //@ close principal(receiver, _);
}

#endif
