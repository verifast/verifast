#include "nsl.h"

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

int random_stub_nsl(void *havege_state, char *output, size_t len)
  //@ requires PRG_PRECONDITION(havege_state_initialized, havege_state);
  //@ ensures PRG_POSTCONDITION(havege_state_initialized, havege_state);
{
  return havege_random(havege_state, output, len);
}

/*@

#define GENERAL_PRE(PRINCIPAL) \
  [_]public_invar(nsl_pub) &*& \
  [_]decryption_key_classifier(nsl_public_key) &*& \
  principal(PRINCIPAL, ?p_id) &*& \
  integer(socket, ?s) &*& \
    net_status(s, nil, ?port, connected) &*& \
  havege_state_initialized(havege_state) \

#define GENERAL_POST(PRINCIPAL) \
  principal(PRINCIPAL, _) &*& \
  integer(socket, s) &*& \
    net_status(s, nil, port, connected) &*& \
  havege_state_initialized(havege_state) \

@*/

/*@
predicate sender_inter(list<crypto_char> r_nonce_ccs, cryptogram r_nonce_cg) = true;

#define SENDER_INTER \
  sender_inter(?r_nonce_ccs, ?r_nonce_cg) &*& \
  ( \
    col || bad(sender) || bad(recvr) ? \
      crypto_chars(normal, r_nonce, NONCE_SIZE, r_nonce_ccs) \
    : \
      cryptogram(r_nonce, NONCE_SIZE, r_nonce_ccs, r_nonce_cg) &*& \
      r_nonce_cg == cg_nonce(recvr, _) &*& \
      cg_info(r_nonce_cg) == int_pair(2, int_pair(sender, int_pair(sender, \
                                         int_pair(recvr, r_id)))) \
  )
@*/

void sender_msg1(int* socket, havege_state* havege_state, pk_context* r_context,
                 int sender, char* s_nonce)
  /*@ requires GENERAL_PRE(sender) &*&
               pk_context_with_key(r_context, pk_public,
                                   ?receiver, ?r_id, 8 * KEY_SIZE) &*&
               cryptogram(s_nonce, NONCE_SIZE, ?s_nonce_ccs, ?s_nonce_cg) &*&
                 s_nonce_cg == cg_nonce(sender, _) &*&
                 cg_info(s_nonce_cg) == int_pair(1, int_pair(receiver, r_id)); @*/
  /*@ ensures  GENERAL_POST(sender) &*&
               pk_context_with_key(r_context, pk_public,
                                   receiver, r_id, 8 * KEY_SIZE) &*&
               cryptogram(s_nonce, NONCE_SIZE, s_nonce_ccs, s_nonce_cg); @*/
{
  //@ open principal(sender, _);
  size_t size;
  char message[MSG1_SIZE];
  char encrypted[KEY_SIZE];

  // Construct the message
  write_identifier(message, sender);
  //@ list<crypto_char> sid_ccs = cs_to_ccs(identifier(sender));
  //@ assert crypto_chars(normal, message, ID_SIZE, sid_ccs);
  //@ cs_to_ccs_crypto_chars(message, identifier(sender));
  //@ public_chars(message, ID_SIZE);
  //@ chars_to_secret_crypto_chars(message, ID_SIZE);

  //@ open cryptogram(s_nonce, NONCE_SIZE, s_nonce_ccs, s_nonce_cg);
  crypto_memcpy((void*) message + ID_SIZE, s_nonce, NONCE_SIZE);
  //@ crypto_chars_join(message);
  //@ list<crypto_char> msg1 = append(sid_ccs, s_nonce_ccs);
  //@ assert crypto_chars(secret, message, MSG1_SIZE, msg1);

   // Encrypt the message
  /*@ produce_function_pointer_chunk random_function(random_stub_nsl)
                    (havege_state_initialized)(state, out, len) { call(); } @*/
  //@ close random_state_predicate(havege_state_initialized);
  if (pk_encrypt(r_context, message, MSG1_SIZE, encrypted, &size,
                  KEY_SIZE, random_stub_nsl, havege_state) != 0)
    abort();
  //@ assert size |-> ?size_val;
  //@ assert cryptogram(encrypted, size_val, ?cs_enc, ?cg_enc);

  // Proof the message is public
  //@ take_append(ID_SIZE, sid_ccs, s_nonce_ccs);
  //@ drop_append(ID_SIZE, sid_ccs, s_nonce_ccs);
  //@ close nsl_pub_msg_sender(sender);
  //@ leak nsl_pub_msg_sender(sender);
  /*@ if (col || bad(sender) || bad(receiver))
      {
        assert crypto_chars(secret, message, MSG1_SIZE, msg1);
        crypto_chars_split(message, ID_SIZE);
        public_crypto_chars(message, ID_SIZE);
        assert chars(message, ID_SIZE, ?sid_cs);
        cs_to_ccs_inj(sid_cs, identifier(sender));
        assert chars(message, ID_SIZE, identifier(sender));
        close nsl_pub(s_nonce_cg);
        leak nsl_pub(s_nonce_cg);

        close cryptogram((void*) message + ID_SIZE, NONCE_SIZE,
                          s_nonce_ccs, s_nonce_cg);
        public_cryptogram((void*) message + ID_SIZE, s_nonce_cg);
        assert chars((void*) message + ID_SIZE, NONCE_SIZE, ?s_nonce_cs');
        cs_to_ccs_append(identifier(sender), s_nonce_cs');
        chars_join(message);
        public_chars(message, MSG1_SIZE);
        chars_to_crypto_chars(message, MSG1_SIZE);
      }
      else
      {
        close nsl_pub_msg1(sender, receiver, s_nonce_cg);
      }
  @*/
  //@ close nsl_pub(cg_enc);
  //@ leak nsl_pub(cg_enc);
  //@ public_cryptogram(encrypted, cg_enc);

  // Send the message
  net_send(socket, encrypted, size);
  zeroize(message, MSG1_SIZE);
  //@ close cryptogram(s_nonce, NONCE_SIZE, s_nonce_ccs, s_nonce_cg);
  //@ close principal(sender, _);
  
  //@ chars_join(encrypted);
}

void sender_msg2(int* socket, havege_state* havege_state, pk_context* s_context,
                 int sender, int recvr, char* s_nonce, char* r_nonce)
  /*@ requires GENERAL_PRE(sender) &*&
               pk_context_with_key(s_context, pk_private,
                                   sender, ?s_id, 8 * KEY_SIZE)  &*&
               pk_context_with_key(?r_context, pk_public,
                                   recvr, ?r_id, 8 * KEY_SIZE)  &*&
               cryptogram(s_nonce, NONCE_SIZE, ?s_nonce_ccs, ?s_nonce_cg) &*&
                 s_nonce_cg == cg_nonce(sender, _) &*&
                 cg_info(s_nonce_cg) == int_pair(1, int_pair(recvr, r_id)) &*&
               chars_(r_nonce, NONCE_SIZE, _); @*/
  /*@ ensures  GENERAL_POST(sender) &*&
               pk_context_with_key(s_context, pk_private,
                                   sender, s_id, 8 * KEY_SIZE) &*&
               pk_context_with_key(r_context, pk_public,
                                   recvr, r_id, 8 * KEY_SIZE)  &*&
               cryptogram(s_nonce, NONCE_SIZE, s_nonce_ccs, s_nonce_cg) &*&
               SENDER_INTER; @*/
{
  //@ open principal(sender, _);
  size_t size;
  char message[MSG2_SIZE];
  char encrypted[KEY_SIZE];

  // Receive the message
  if (net_recv(socket, encrypted, KEY_SIZE) != KEY_SIZE)
    abort();
  //@ assert chars(encrypted, KEY_SIZE, ?enc_cs);
  //@ interpret_asym_encrypted(encrypted, KEY_SIZE);
  //@ assert cryptogram(encrypted, KEY_SIZE, ?enc_ccs, ?enc_cg);

  // Decrypt the message
  /*@ produce_function_pointer_chunk random_function(random_stub_nsl)
                    (havege_state_initialized)(state, out, len) { call(); } @*/
  //@ close random_state_predicate(havege_state_initialized);
  //@ structure st = known_value(0, cs_to_ccs(identifier(recvr)));
  //@ close decryption_pre(false, false, sender, st, enc_ccs);
  if (pk_decrypt(s_context, encrypted, KEY_SIZE, message,
                  &size, MSG2_SIZE, random_stub_nsl, havege_state) != 0)
    abort();
  if (size != MSG2_SIZE)
    abort();
  //@ public_cryptogram(encrypted, enc_cg);
  //@ assert enc_cg == cg_rsa_encrypted(?p, ?c, ?pay, ?ent);
  //@ assert size |-> MSG2_SIZE;
  /*@ open decryption_post(false, ?garbage, sender,
                           st, sender, s_id, ?dec_ccs); @*/
  //@ assert crypto_chars(?kind, message, MSG2_SIZE, dec_ccs);
  //@ crypto_chars_split(message, ID_SIZE);
  //@ crypto_chars_split((void*) message + ID_SIZE, NONCE_SIZE);
  //@ assert crypto_chars(kind, message, ID_SIZE, ?id_ccs);
  //@ assert crypto_chars(kind, (void*) message + ID_SIZE, NONCE_SIZE, ?s_ccs);
  /*@ assert crypto_chars(kind, (void*) message + ID_SIZE + NONCE_SIZE,
                          NONCE_SIZE, ?r_ccs); @*/
  //@ append_assoc(id_ccs, s_ccs, r_ccs);
  //@ take_append(ID_SIZE, id_ccs, append(s_ccs, r_ccs));
  //@ drop_append(ID_SIZE, id_ccs, append(s_ccs, r_ccs));
  //@ take_append(NONCE_SIZE, s_ccs, r_ccs);
  //@ drop_append(NONCE_SIZE, s_ccs, r_ccs);

  // Interpret the message
  //@ open [_]nsl_pub(enc_cg);
  //@ assert [_]nsl_pub_msg_sender(?recvr2);
  /*@ if (col || garbage)
      {
        crypto_chars_to_chars(message, ID_SIZE);
        crypto_chars_to_chars((void*) message + ID_SIZE, NONCE_SIZE);
        chars_to_crypto_chars((void*) message + ID_SIZE, NONCE_SIZE);
        crypto_chars_to_chars((void*) message + ID_SIZE + NONCE_SIZE, NONCE_SIZE);
        chars_to_crypto_chars((void*) message + ID_SIZE + NONCE_SIZE, NONCE_SIZE);
        MEMCMP_PUB((void*) message + ID_SIZE)
      }
      else
      {
        if (bad(sender) || bad(recvr2))
        {
          assert [_]public_ccs(dec_ccs);
          public_ccs_split(dec_ccs, ID_SIZE);
          public_ccs_split(append(s_ccs, r_ccs), NONCE_SIZE);
          public_crypto_chars((void*) message + ID_SIZE, NONCE_SIZE);
          chars_to_crypto_chars((void*) message + ID_SIZE, NONCE_SIZE);
          MEMCMP_PUB((void*) message + ID_SIZE)
        }
        else
        {
          assert [_]nsl_pub_msg2(sender, recvr2, ?s_nonce_cg2, ?s_nonce_ccs2,
                                 ?r_nonce_cg, _, _, _, ?pub_ns);
          take_append(ID_SIZE, cs_to_ccs(identifier(recvr2)),
                      append(s_nonce_ccs2, ccs_for_cg(r_nonce_cg)));
          drop_append(ID_SIZE, cs_to_ccs(identifier(recvr2)),
                      append(s_nonce_ccs2, ccs_for_cg(r_nonce_cg)));
          take_append(NONCE_SIZE, s_nonce_ccs2, ccs_for_cg(r_nonce_cg));
          drop_append(NONCE_SIZE, s_nonce_ccs2, ccs_for_cg(r_nonce_cg));
          if (pub_ns)
          {
            public_crypto_chars((void*) message + ID_SIZE, NONCE_SIZE);
            chars_to_crypto_chars((void*) message + ID_SIZE, NONCE_SIZE);
            MEMCMP_PUB((void*) message + ID_SIZE)
          }
          else
          {
            close exists(s_nonce_cg2);
            leak exists(s_nonce_cg2);
            sublist_refl(s_nonce_ccs2);
            MEMCMP_REGION(cons(memcmp_sec(s_nonce_cg2), nil), s_nonce_ccs2)
          }
        }
        public_crypto_chars(message, ID_SIZE);
      }
  @*/
  //@ chars_to_crypto_chars(message, ID_SIZE);
  /*@ close check_identifier_ghost_args(false, garbage, sender, sender,
                                        s_id, append(s_ccs, r_ccs)); @*/
  check_identifier(message, recvr);
  //@ open cryptogram(s_nonce, NONCE_SIZE, s_nonce_ccs, s_nonce_cg);
  //@ MEMCMP_SEC(s_nonce, s_nonce_cg)
  if (crypto_memcmp((void*) message + ID_SIZE, s_nonce, NONCE_SIZE) != 0) abort();
  crypto_memcpy(r_nonce, (void*) message + ID_SIZE + NONCE_SIZE, NONCE_SIZE);
  //@ assert id_ccs == cs_to_ccs(identifier(recvr));
  //@ assert s_ccs == s_nonce_ccs;
  //@ cryptogram r_nonce_cg = ccs_for_cg_sur(r_ccs, tag_nonce);
  //@ close sender_inter(r_ccs, r_nonce_cg);

  /*@ if (!col && !garbage)
      {
        if (bad(sender) || bad(recvr2))
        {
          assert [_]public_ccs(dec_ccs);
          public_ccs_split(dec_ccs, ID_SIZE);
          public_ccs_split(append(s_nonce_ccs, r_ccs), NONCE_SIZE);
          public_crypto_chars(r_nonce, NONCE_SIZE);
          chars_to_crypto_chars(r_nonce, NONCE_SIZE);
          public_ccs_cg(s_nonce_cg);
          open [_]nsl_pub(s_nonce_cg);
          crypto_chars_to_chars((void*) message + ID_SIZE, NONCE_SIZE);
          chars_to_secret_crypto_chars((void*) message + ID_SIZE, NONCE_SIZE);
        }
        else
        {
          assert dec_ccs == pay;
          assert sender == p;
          assert s_id == c;
          assert [_]nsl_pub_msg2(sender, recvr2, ?s_nonce_cg2, ?s_nonce_ccs2,
                                 ?r_nonce_cg2, ?p_inst, ?p2, ?c2, ?pub_ns);
          cs_to_ccs_inj(identifier(recvr2), identifier(recvr));
          assert identifier(recvr) == identifier(recvr2);
          equal_identifiers(recvr, recvr2);
          if (pub_ns)
          {
            public_ccs_cg(s_nonce_cg);
            open [_]nsl_pub(s_nonce_cg);
            assert false;
          }
          ccs_for_cg_inj(r_nonce_cg2, r_nonce_cg);
          close cryptogram(r_nonce, NONCE_SIZE, r_ccs, r_nonce_cg2);
          ccs_for_cg_inj(s_nonce_cg, s_nonce_cg2);
          assert c2 == r_id;
        }
      }
  @*/

  //@ close cryptogram(s_nonce, NONCE_SIZE, s_nonce_ccs, s_nonce_cg);
  //@ crypto_chars_join((void*) message + ID_SIZE);
  zeroize((void*) message + ID_SIZE, 2 * NONCE_SIZE);
  //@ crypto_chars_to_chars(message, ID_SIZE);
  //@ chars_join(message);
  //@ close principal(sender, _);
}

void sender_msg3(int* socket, havege_state* havege_state, pk_context* r_context,
                 int sender, char* r_nonce)
  /*@ requires GENERAL_PRE(sender) &*&
               pk_context_with_key(r_context, pk_public,
                                   ?recvr, ?r_id, 8 * KEY_SIZE) &*&
               SENDER_INTER; @*/
  /*@ ensures  GENERAL_POST(sender) &*&
               pk_context_with_key(r_context, pk_public,
                                   recvr, r_id, 8 * KEY_SIZE) &*&
               col || bad(sender) || bad(recvr) ?
                 chars(r_nonce, NONCE_SIZE, ?r_nonce_cs) &*&
                 r_nonce_ccs == cs_to_ccs(r_nonce_cs)
               :
                 cryptogram(r_nonce, NONCE_SIZE, r_nonce_ccs, r_nonce_cg); @*/
{
  //@ open principal(sender, _);
  size_t size;
  char message[MSG3_SIZE];
  char encrypted[KEY_SIZE];

  // Construct the message
  //@ open sender_inter(r_nonce_ccs, r_nonce_cg);
  //@ bool condition = col || bad(sender) || bad(recvr);
  /*@ if (!condition)
        open cryptogram(r_nonce, NONCE_SIZE, r_nonce_ccs, r_nonce_cg);
      else
      {
        crypto_chars_to_chars(r_nonce, NONCE_SIZE);
        public_chars(r_nonce, NONCE_SIZE);
        chars_to_secret_crypto_chars(r_nonce, NONCE_SIZE);
      }
  @*/
  crypto_memcpy(message, r_nonce, NONCE_SIZE);
  /*@ if (!condition)
        close cryptogram(r_nonce, NONCE_SIZE, r_nonce_ccs, r_nonce_cg);
      else
        public_crypto_chars(r_nonce, NONCE_SIZE);
  @*/

  // Encrypt the message
  /*@ produce_function_pointer_chunk random_function(random_stub_nsl)
                    (havege_state_initialized)(state, out, len) { call(); } @*/
  //@ close random_state_predicate(havege_state_initialized);
  if (pk_encrypt(r_context, message, MSG3_SIZE, encrypted, &size,
                 KEY_SIZE, random_stub_nsl, havege_state) != 0)
    abort();
  //@ assert size |-> ?size_val;
  //@ assert cryptogram(encrypted, size_val, ?cs_enc, ?cg_enc);

  // Proof the message is public
  //@ close nsl_pub_msg_sender(sender);
  //@ leak nsl_pub_msg_sender(sender);
  //@ if (!condition) close nsl_pub_msg3(sender, recvr, r_nonce_cg);
  //@ close nsl_pub(cg_enc);
  //@ leak nsl_pub(cg_enc);
  //@ public_cryptogram(encrypted, cg_enc);

  // Send the message
  net_send(socket, encrypted, size);
  zeroize(message, MSG3_SIZE);
  //@ close principal(sender, _);
  //@ chars_join(encrypted);
}

void sender(int sender, int receiver,
            char *s_priv_key, char *r_pub_key,
            char *s_nonce, char *r_nonce)
/*@ requires [_]public_invar(nsl_pub) &*&
             [_]decryption_key_classifier(nsl_public_key) &*&
             principal(sender, _) &*&
             [?f1]cryptogram(s_priv_key, 8 * KEY_SIZE,
                             ?s_priv_key_ccs, ?s_priv_key_cg) &*&
               s_priv_key_cg == cg_rsa_private_key(sender, ?s_id) &*&
             [?f2]cryptogram(r_pub_key, 8 * KEY_SIZE,
                             ?r_pub_key_ccs, ?r_pub_key_cg) &*&
               r_pub_key_cg == cg_rsa_public_key(receiver, ?r_id) &*&
             chars_(s_nonce, NONCE_SIZE, _) &*&
             chars_(r_nonce, NONCE_SIZE, _); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(s_priv_key, 8 * KEY_SIZE,
                            s_priv_key_ccs, s_priv_key_cg) &*&
             [f2]cryptogram(r_pub_key, 8 * KEY_SIZE,
                            r_pub_key_ccs, r_pub_key_cg) &*&
             cryptogram(s_nonce, NONCE_SIZE, ?s_nonce_ccs, ?s_nonce_cg) &*&
               s_nonce_cg == cg_nonce(sender, _) &*&
               cg_info(s_nonce_cg) == int_pair(1, int_pair(receiver, r_id)) &*&
             col || bad(sender) || bad(receiver) ?
               chars(r_nonce, NONCE_SIZE, _)
             :
               cryptogram(r_nonce, NONCE_SIZE, _, ?r_nonce_cg) &*&
               r_nonce_cg == cg_nonce(receiver, _) &*&
               cg_info(r_nonce_cg) == int_pair(2, int_pair(sender, int_pair(sender,
                                                  int_pair(receiver, r_id)))); @*/
{
  int socket;
  pk_context s_context;
  pk_context r_context;
  havege_state havege_state;

  net_usleep(20000);
  if(net_connect(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();

  //@ close pk_context(&s_context);
  pk_init(&s_context);
  if (pk_parse_key(&s_context, s_priv_key,
                   (unsigned int) 8 * KEY_SIZE, NULL, 0) != 0)
    abort();
  //@ close pk_context(&r_context);
  pk_init(&r_context);
  if (pk_parse_public_key(&r_context, r_pub_key,
                          (unsigned int) 8 * KEY_SIZE) != 0)
    abort();

  // Generate NA
  //@ open principal(sender, _);
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  //@ close random_request(sender, int_pair(1, int_pair(receiver, r_id)), false);
  if (havege_random(&havege_state, s_nonce, NONCE_SIZE) != 0) abort();
  //@ assert cryptogram(s_nonce, NONCE_SIZE, ?cs_s_nonce, ?cg_s_nonce);
  //@ close principal(sender, _);

  sender_msg1(&socket, &havege_state, &r_context, sender, s_nonce);
  sender_msg2(&socket, &havege_state, &s_context, sender, receiver,
              s_nonce, r_nonce);
  sender_msg3(&socket, &havege_state, &r_context, sender, r_nonce);
  havege_free(&havege_state);
  //@ open havege_state(&havege_state);

  //@ pk_release_context_with_key(&s_context);
  pk_free(&s_context);
  //@ open pk_context(&s_context);
  //@ pk_release_context_with_key(&r_context);
  pk_free(&r_context);
  //@ open pk_context(&r_context);

  net_close(socket);
}

/*@
predicate receiver_inter(int p_original, int c_original, int p_instigator,
                         list<crypto_char> s_nonce_ccs, cryptogram s_nonce_cg) = true;

#define RECEIVER_INTER \
  ( \
    receiver_inter(?p_orig, ?c_orig, ?p_inst, ?s_nonce_ccs, ?s_nonce_cg) &*& \
    col || bad(p_inst) || bad(receiver) ? \
      crypto_chars(normal, s_nonce, NONCE_SIZE, s_nonce_ccs) \
    : \
      receiver == p_orig && r_id == c_orig &*& \
      cryptogram(s_nonce, NONCE_SIZE, s_nonce_ccs, s_nonce_cg) &*& \
      sender == p_inst &*& s_nonce_cg == cg_nonce(sender, _) &*& \
      cg_info(s_nonce_cg) == int_pair(1, int_pair(receiver, r_id)) \
  )
@*/

void receiver_msg1(int* socket, havege_state* havege_state,
                   pk_context* r_context, int sender, int receiver,
                   char* s_nonce)
  /*@ requires GENERAL_PRE(receiver) &*&
               pk_context_with_key(r_context, pk_private,
                                   receiver, ?r_id, 8 * KEY_SIZE)  &*&
               chars_(s_nonce, NONCE_SIZE, _); @*/
  /*@ ensures  GENERAL_POST(receiver) &*&
               pk_context_with_key(r_context, pk_private,
                                   receiver, r_id, 8 * KEY_SIZE) &*&
               RECEIVER_INTER; @*/
{
  //@ open principal(receiver, _);
  size_t size;
  char message[MSG1_SIZE];
  char encrypted[KEY_SIZE];

  // Receive the message
  if (net_recv(socket, encrypted, KEY_SIZE) != KEY_SIZE)
    abort();
  //@ assert chars(encrypted, KEY_SIZE, ?enc_cs);
  //@ interpret_asym_encrypted(encrypted, KEY_SIZE);
  //@ assert cryptogram(encrypted, KEY_SIZE, ?enc_ccs, ?enc_cg);
  //@ assert enc_cg == cg_rsa_encrypted(?p, ?c, ?pay, ?ent);

  // Decrypt the message
  /*@ produce_function_pointer_chunk random_function(random_stub_nsl)
                    (havege_state_initialized)(state, out, len) { call(); } @*/
  //@ close random_state_predicate(havege_state_initialized);
  //@ structure st = known_value(0, cs_to_ccs(identifier(sender)));
  //@ close decryption_pre(false, false, receiver, st, enc_ccs);
  if (pk_decrypt(r_context, encrypted, KEY_SIZE, message,
                  &size, MSG1_SIZE, random_stub_nsl, havege_state) != 0)
    abort();
  if (size != MSG1_SIZE)
    abort();
  //@ assert size |-> MSG1_SIZE;
  //@ assert crypto_chars(?kind, message, MSG1_SIZE, ?dec_ccs);
  /*@ open decryption_post(false, ?garbage, receiver,
                           st, receiver, r_id, dec_ccs); @*/
  //@ crypto_chars_split(message, ID_SIZE);
  //@ assert crypto_chars(kind, message, ID_SIZE, ?id_ccs);
  /*@ assert crypto_chars(kind, (void*) message + ID_SIZE,
                          NONCE_SIZE, ?s_nonce_ccs); @*/
  //@ assert dec_ccs == append(id_ccs, s_nonce_ccs);

  //@ open [_]nsl_pub(enc_cg);
  //@ assert [_]nsl_pub_msg_sender(?p_instigator2);
  /*@ if (col || garbage)
      {
        crypto_chars_to_chars(message, ID_SIZE);
      }
      else
      {
        if (bad(receiver) || bad(p_instigator2))
        {
          assert [_]public_ccs(dec_ccs);
          public_ccs_split(dec_ccs, ID_SIZE);
        }
        else
        {
          assert [_]nsl_pub_msg1(_, _, ?s_nonce_cg);
          take_append(ID_SIZE, cs_to_ccs(identifier(p_instigator2)),
                      ccs_for_cg(s_nonce_cg));
          drop_append(ID_SIZE, cs_to_ccs(identifier(p_instigator2)),
                      ccs_for_cg(s_nonce_cg));
        }
        public_crypto_chars(message, ID_SIZE);
      }
  @*/
  //@ chars_to_crypto_chars(message, ID_SIZE);
  /*@ close check_identifier_ghost_args(false, garbage, receiver, receiver,
                                        r_id, s_nonce_ccs); @*/
  check_identifier(message, sender);
  //@ assert id_ccs == cs_to_ccs(identifier(sender));
  crypto_memcpy(s_nonce, (void*) message + ID_SIZE, NONCE_SIZE);

  // Interpret message
  //@ cryptogram s_nonce_cg;
  //@ int p_inst;
  /*@ if (!col && !garbage)
      {
        p_inst = p_instigator2;
        if (bad(p_inst) || bad(receiver))
        {
          public_crypto_chars(s_nonce, NONCE_SIZE);
          chars_to_crypto_chars(s_nonce, NONCE_SIZE);
          crypto_chars_to_chars(message, ID_SIZE);
          chars_to_crypto_chars(message, ID_SIZE);
          public_crypto_chars((void*) message + ID_SIZE, NONCE_SIZE);
          chars_to_crypto_chars((void*) message + ID_SIZE, NONCE_SIZE);
        }
        else
        {
          assert [_]nsl_pub_msg1(p_inst, receiver, ?s_nonce_cg2);
          s_nonce_cg = s_nonce_cg2;
          assert s_nonce_cg == cg_nonce(p_inst, _);
          s_nonce_ccs = ccs_for_cg(s_nonce_cg);
          assert dec_ccs == append(cs_to_ccs(identifier(p_inst)), s_nonce_ccs);
          take_append(ID_SIZE, cs_to_ccs(identifier(p_inst)), s_nonce_ccs);
          drop_append(ID_SIZE, cs_to_ccs(identifier(p_inst)), s_nonce_ccs);
          cs_to_ccs_inj(identifier(p_inst), identifier(sender));
          assert identifier(p_inst) == identifier(sender);
          equal_identifiers(p_inst, sender);
          close cryptogram(s_nonce, NONCE_SIZE, s_nonce_ccs, s_nonce_cg);
        }
      }
      else
      {
        crypto_chars_to_chars(s_nonce, NONCE_SIZE);
        chars_to_crypto_chars(s_nonce, NONCE_SIZE);
      }
  @*/
  //@ close receiver_inter(p, c, p_inst, s_nonce_ccs, s_nonce_cg);
  //@ crypto_chars_to_chars(message, ID_SIZE);
  zeroize((void*) message + ID_SIZE, NONCE_SIZE);
  //@ public_cryptogram(encrypted, enc_cg);
  //@ close principal(receiver, _);
  //@ chars_join(message);
}

void receiver_msg2(int* socket, havege_state* havege_state,
                   pk_context* s_context, int receiver,
                   char* s_nonce, char* r_nonce)
  /*@ requires GENERAL_PRE(receiver) &*&
               pk_context_with_key(?r_context, pk_private,
                                   receiver, ?r_id, 8 * KEY_SIZE)  &*&
               pk_context_with_key(s_context, pk_public,
                                   ?sender, ?s_id, 8 * KEY_SIZE) &*&
               RECEIVER_INTER &*&
               cryptogram(r_nonce, NONCE_SIZE, ?r_nonce_ccs, ?r_nonce_cg) &*&
                 r_nonce_cg == cg_nonce(receiver, _) &*&
                 cg_info(r_nonce_cg) == int_pair(2, int_pair(sender,
                               int_pair(p_inst, int_pair(p_orig, c_orig)))); @*/
  /*@ ensures  GENERAL_POST(receiver) &*&
               pk_context_with_key(r_context, pk_private,
                                   receiver, r_id, 8 * KEY_SIZE)  &*&
               pk_context_with_key(s_context, pk_public,
                                   sender, s_id, 8 * KEY_SIZE) &*&
               (
                  col || bad(p_inst) || bad(receiver) ?
                    chars(s_nonce, NONCE_SIZE, ?s_nonce_cs) &*&
                    s_nonce_ccs == cs_to_ccs(s_nonce_cs)
                  :
                    cryptogram(s_nonce, NONCE_SIZE, s_nonce_ccs, s_nonce_cg)
               ) &*&
               cryptogram(r_nonce, NONCE_SIZE, r_nonce_ccs, r_nonce_cg); @*/
{
  //@ open principal(receiver, _);
  size_t size;
  char message[MSG2_SIZE];
  char encrypted[KEY_SIZE];
  //@ open receiver_inter(p_orig, c_orig, p_inst, s_nonce_ccs, s_nonce_cg);

  // Construct the message
  write_identifier(message, receiver);
  //@ list<crypto_char> rid_ccs = cs_to_ccs(identifier(receiver));
  //@ assert crypto_chars(normal, message, ID_SIZE, rid_ccs);
  //@ cs_to_ccs_crypto_chars(message, identifier(receiver));
  //@ public_chars(message, ID_SIZE);
  //@ chars_to_secret_crypto_chars(message, ID_SIZE);
  //@ bool condition =  col || bad(p_inst) || bad(receiver);
  /*@ if (!condition)
        open cryptogram(s_nonce, NONCE_SIZE, s_nonce_ccs, s_nonce_cg);
      else
      {
        crypto_chars_to_chars(s_nonce, NONCE_SIZE);
        public_chars(s_nonce, NONCE_SIZE);
        chars_to_secret_crypto_chars(s_nonce, NONCE_SIZE);
      }
  @*/
  //@ open cryptogram(r_nonce, NONCE_SIZE, r_nonce_ccs, r_nonce_cg);
  crypto_memcpy((void*) message + ID_SIZE, s_nonce, NONCE_SIZE);
  crypto_memcpy((void*) message + ID_SIZE + NONCE_SIZE, r_nonce, NONCE_SIZE);
  //@ crypto_chars_join(message);
  //@ crypto_chars_join(message);
  //@ list<crypto_char> msg2 = append(rid_ccs, append(s_nonce_ccs, r_nonce_ccs));
  //@ append_assoc(rid_ccs, s_nonce_ccs, r_nonce_ccs);
  //@ assert crypto_chars(secret, message, MSG2_SIZE, msg2);

  // Encrypt the message
  /*@ produce_function_pointer_chunk random_function(random_stub_nsl)
                    (havege_state_initialized)(state, out, len) { call(); } @*/
  //@ close random_state_predicate(havege_state_initialized);
  if (pk_encrypt(s_context, message, MSG2_SIZE, encrypted, &size,
                  KEY_SIZE, random_stub_nsl, havege_state) != 0)
    abort();
  //@ assert size |-> ?size_val;
  //@ assert cryptogram(encrypted, size_val, ?cs_enc, ?cg_enc);
  //@ take_append(ID_SIZE, rid_ccs, append(s_nonce_ccs, r_nonce_ccs));
  //@ drop_append(ID_SIZE, rid_ccs, append(s_nonce_ccs, r_nonce_ccs));
  //@ take_append(NONCE_SIZE, s_nonce_ccs, r_nonce_ccs);
  //@ drop_append(NONCE_SIZE, s_nonce_ccs, r_nonce_ccs);

  // Proof the message is public
  /*@ if (col || bad(sender) || bad(receiver))
      {
        assert crypto_chars(secret, message, MSG2_SIZE, msg2);
        crypto_chars_split(message, ID_SIZE);
        crypto_chars_split((void*) message + ID_SIZE, NONCE_SIZE);
        public_crypto_chars((void*) message, ID_SIZE);
        public_crypto_chars((void*) message + ID_SIZE, NONCE_SIZE);
        close nsl_pub(r_nonce_cg);
        leak nsl_pub(r_nonce_cg);
        close cryptogram((void*) message + ID_SIZE + NONCE_SIZE, NONCE_SIZE,
                         r_nonce_ccs, r_nonce_cg);
        public_cryptogram((void*) message + ID_SIZE + NONCE_SIZE, r_nonce_cg);
        
        assert chars((void*) message, ID_SIZE, ?rid_cs);
        assert chars((void*) message + ID_SIZE, NONCE_SIZE, ?s_nonce_cs);
        assert chars((void*) message + ID_SIZE + NONCE_SIZE, NONCE_SIZE, ?r_nonce_cs);        
        cs_to_ccs_append(rid_cs, s_nonce_cs);
        cs_to_ccs_append(append(rid_cs, s_nonce_cs), r_nonce_cs);

        chars_join(message);
        chars_join(message);
        public_chars(message, MSG2_SIZE);
        chars_to_secret_crypto_chars(message, MSG2_SIZE);
      }
      else
      {
        close nsl_pub_msg2(sender, receiver, s_nonce_cg, s_nonce_ccs, r_nonce_cg,
                           p_inst, p_orig, c_orig, condition);
      }
  @*/
  //@ close nsl_pub_msg_sender(receiver);
  //@ leak nsl_pub_msg_sender(receiver);
  //@ close nsl_pub(cg_enc);
  //@ leak nsl_pub(cg_enc);
  //@ public_cryptogram(encrypted, cg_enc);

  // Send the message
  net_send(socket, encrypted, size);
  zeroize(message, MSG2_SIZE);

  /*@ if (!condition)
        close cryptogram(s_nonce, NONCE_SIZE, s_nonce_ccs, s_nonce_cg);
      else
        public_crypto_chars(s_nonce, NONCE_SIZE);
  @*/
  //@ close cryptogram(r_nonce, NONCE_SIZE, r_nonce_ccs, r_nonce_cg);
  //@ close principal(receiver, _);
  //@ chars_join(encrypted);
}

void receiver_msg3(int* socket, havege_state* havege_state,
                   pk_context* r_context, int sender, int receiver,
                   char* s_nonce, char* r_nonce)
  /*@ requires GENERAL_PRE(receiver) &*&
               pk_context_with_key(r_context, pk_private,
                                   receiver, ?r_id, 8 * KEY_SIZE)  &*&
               RECEIVER_INTER &*&
               cryptogram(r_nonce, NONCE_SIZE, ?r_nonce_ccs, ?r_nonce_cg) &*&
                 r_nonce_cg == cg_nonce(receiver, _) &*&
                 cg_info(r_nonce_cg) == int_pair(2, int_pair(sender,
                               int_pair(p_inst, int_pair(p_orig, c_orig)))); @*/
  /*@ ensures  GENERAL_POST(receiver) &*&
               pk_context_with_key(r_context, pk_private,
                                   receiver, r_id, 8 * KEY_SIZE) &*&
               (
                 col || bad(p_inst) || bad(receiver) ?
                   crypto_chars(normal, s_nonce, NONCE_SIZE, s_nonce_ccs)
                 :
                   cryptogram(s_nonce, NONCE_SIZE, s_nonce_ccs, s_nonce_cg)
               ) &*&
               cryptogram(r_nonce, NONCE_SIZE, r_nonce_ccs, r_nonce_cg) &*&
               col || bad(sender) || bad(receiver) ||
                 (receiver == p_orig && r_id == c_orig && sender == p_inst); @*/
{
  //@ open principal(receiver, _);
  size_t size;
  char message[MSG3_SIZE];
  char encrypted[KEY_SIZE];
  //@ open receiver_inter(p_orig, c_orig, p_inst, s_nonce_ccs, s_nonce_cg);

  // Receive the message
  if (net_recv(socket, encrypted, KEY_SIZE) != KEY_SIZE)
    abort();
  //@ assert chars(encrypted, KEY_SIZE, ?enc_cs);
  //@ interpret_asym_encrypted(encrypted, KEY_SIZE);
  //@ assert cryptogram(encrypted, KEY_SIZE, ?enc_ccs, ?enc_cg);
  //@ assert enc_cg == cg_rsa_encrypted(?p, ?c, ?pay, ?ent);

  // Decrypt the message
  /*@ produce_function_pointer_chunk random_function(random_stub_nsl)
                    (havege_state_initialized)(state, out, len) { call(); } @*/
  //@ close random_state_predicate(havege_state_initialized);
  //@ structure st = known_value(0, r_nonce_ccs);
  //@ close decryption_pre(false, false, receiver, st, enc_ccs);
  if (pk_decrypt(r_context, encrypted, KEY_SIZE, message,
                  &size, MSG3_SIZE, random_stub_nsl, havege_state) != 0)
    abort();
  if (size != MSG3_SIZE)
    abort();
  //@ assert size |-> MSG3_SIZE;
  //@ assert crypto_chars(?kind, message, NONCE_SIZE, ?dec_ccs);
  /*@ open decryption_post(false, ?garbage, receiver,
                           st, receiver, r_id, dec_ccs); @*/

  // Interpret the message
  //@ open cryptogram(r_nonce, NONCE_SIZE, r_nonce_ccs, r_nonce_cg);
  //@ open [_]nsl_pub(enc_cg);
  //@ assert [_]nsl_pub_msg_sender(?sender2);
  /*@ if (col || garbage)
      {
        crypto_chars_to_chars(message, NONCE_SIZE);
        chars_to_crypto_chars(message, NONCE_SIZE);
        MEMCMP_PUB(message)
      }
      else
      {
        if (bad(receiver) || bad(sender2))
        {
          public_crypto_chars(message, NONCE_SIZE);
          chars_to_crypto_chars(message, NONCE_SIZE);
          MEMCMP_PUB(message)
        }
        else
        {
          assert [_]nsl_pub_msg3(sender2, receiver, ?r_nonce_cg2);
          MEMCMP_SEC(message, r_nonce_cg2)
        }
      }
  @*/
  //@ MEMCMP_SEC(r_nonce, r_nonce_cg)
  if (crypto_memcmp((void*) message, r_nonce, NONCE_SIZE) != 0) abort();
  //@ assert dec_ccs == r_nonce_ccs;
  /*@ if (garbage)
      {
        close exists(pair(nil, nil));
        close has_structure(r_nonce_ccs, st);
        leak has_structure(r_nonce_ccs, st);
        decryption_garbage(message, NONCE_SIZE, st);
        crypto_chars_to_chars(message, NONCE_SIZE);
        chars_to_secret_crypto_chars(message, NONCE_SIZE);
      }
      else if (!col && !bad(sender) && !bad(receiver))
      {
        if (bad(receiver) || bad(sender2))
        {
          public_crypto_chars(r_nonce, NONCE_SIZE);
          public_ccs_cg(r_nonce_cg);
          open [_]nsl_pub(r_nonce_cg);
          assert false;
        }
        else if (bad(p_inst))
        {
          assert [_]nsl_pub_msg3(sender2, receiver, ?r_nonce_cg2);
          int p1_1 = int_pair(p_orig, c_orig);
          int p1_2 = int_pair(p_inst, p1_1);
          int p1_3 = int_pair(sender, p1_2);
          int p2_1 = int_pair(receiver, r_id);
          int p2_2 = int_pair(sender2, p2_1);
          int p2_3 = int_pair(sender2, p2_2);
          assert cg_info(r_nonce_cg) == int_pair(2, p1_3);
          assert cg_info(r_nonce_cg2) == int_pair(2, p2_3);
          ccs_for_cg_inj(r_nonce_cg, r_nonce_cg2);
          int_right_int_pair(2, p1_3);
          int_right_int_pair(2, p2_3);
          int_left_int_pair(sender, p1_2);
          int_left_int_pair(sender2, p2_2);
          int_right_int_pair(sender, p1_2);
          int_right_int_pair(sender2, p2_2);
          int_left_int_pair(p_inst, p1_1);
          assert false;
        }
      }
  @*/
  zeroize(message, MSG3_SIZE);
  //@ close cryptogram(r_nonce, NONCE_SIZE, r_nonce_ccs, r_nonce_cg);
  //@ public_cryptogram(encrypted, enc_cg);
  //@ close principal(receiver, _);
}

void receiver(int sender, int receiver,
              char *s_pub_key, char *r_priv_key,
              char *s_nonce, char *r_nonce)
/*@ requires [_]public_invar(nsl_pub) &*&
             [_]decryption_key_classifier(nsl_public_key) &*&
             principal(receiver, _) &*&
             [?f1]cryptogram(s_pub_key, 8 * KEY_SIZE,
                             ?s_pub_key_ccs, ?s_pub_key_cg) &*&
               s_pub_key_cg == cg_rsa_public_key(sender, ?s_id) &*&
             [?f2]cryptogram(r_priv_key, 8 * KEY_SIZE,
                             ?r_priv_key_ccs, ?r_priv_key_cg) &*&
               r_priv_key_cg == cg_rsa_private_key(receiver, ?r_id) &*&
             chars_(s_nonce, NONCE_SIZE, _) &*&
             chars_(r_nonce, NONCE_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(s_pub_key, 8 * KEY_SIZE,
                            s_pub_key_ccs, s_pub_key_cg) &*&
             [f2]cryptogram(r_priv_key, 8 * KEY_SIZE,
                            r_priv_key_ccs, r_priv_key_cg) &*&
             cryptogram(r_nonce, NONCE_SIZE, ?r_nonce_ccs, ?r_nonce_cg) &*&
               r_nonce_cg == cg_nonce(receiver, _) &*&
             (
               col || bad(sender) || bad(receiver) ?
                 chars(s_nonce, NONCE_SIZE, _)
               :
                 cryptogram(s_nonce, NONCE_SIZE, ?s_nonce_ccs, ?s_nonce_cg) &*&
                 s_nonce_cg == cg_nonce(sender, _) &*&
                 cg_info(s_nonce_cg) == int_pair(1, int_pair(receiver, r_id)) &*&
                 cg_info(r_nonce_cg) == int_pair(2, int_pair(sender, int_pair(sender,
                                                    int_pair(receiver, r_id))))
             ); @*/
{
  //@ open principal(receiver, _);
  int socket1;
  int socket2;
  pk_context s_context;
  pk_context r_context;
  havege_state havege_state;

  if(net_bind(&socket1, NULL, SERVER_PORT) != 0)
    abort();
  if(net_accept(socket1, &socket2, NULL) != 0)
    abort();
  if(net_set_block(socket2) != 0)
    abort();

  //@ close pk_context(&s_context);
  pk_init(&s_context);
  if (pk_parse_public_key(&s_context, s_pub_key,
                          (unsigned int) 8 * KEY_SIZE) != 0)
    abort();
  //@ close pk_context(&r_context);
  pk_init(&r_context);
  if (pk_parse_key(&r_context, r_priv_key,
                   (unsigned int) 8 * KEY_SIZE, NULL, 0) != 0)
    abort();

  // Generate NB
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);

  //@ close principal(receiver, _);
  receiver_msg1(&socket2, &havege_state, &r_context, sender, receiver, s_nonce);
  //@ open principal(receiver, _);

  //@ assert receiver_inter(?p_orig, ?c_orig, ?p_inst, ?s_nonce_ccs, ?s_nonce_cg);
  //@ int info = int_pair(sender, int_pair(p_inst, int_pair(p_orig, c_orig)));
  //@ close random_request(receiver, int_pair(2, info), false);
  if (havege_random(&havege_state, r_nonce, NONCE_SIZE) != 0) abort();
  //@ close principal(receiver, _);
  receiver_msg2(&socket2, &havege_state, &s_context, receiver,
                s_nonce, r_nonce);
  //@ if (col || bad(p_inst) || bad(receiver)) chars_to_crypto_chars(s_nonce, NONCE_SIZE);
  //@ close receiver_inter(p_orig, c_orig, p_inst, s_nonce_ccs, s_nonce_cg);
  receiver_msg3(&socket2, &havege_state, &r_context, sender, receiver,
                s_nonce, r_nonce);
  /*@ if (col || bad(sender) || bad(receiver))
        crypto_chars_to_chars(s_nonce, NONCE_SIZE); @*/
  havege_free(&havege_state);
  //@ open havege_state(&havege_state);

  //@ pk_release_context_with_key(&s_context);
  pk_free(&s_context);
  //@ open pk_context(&s_context);
  //@ pk_release_context_with_key(&r_context);
  pk_free(&r_context);
  //@ open pk_context(&r_context);

  net_close(socket2);
  net_close(socket1);
}
