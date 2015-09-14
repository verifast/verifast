#include "nsl.h"

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

#define MSG1_SIZE 12
#define MSG2_SIZE 20
#define MSG3_SIZE 8

int random_stub_nsl(void *havege_state, char *output, size_t len)
  //@ requires PRG_PRECONDITION(havege_state_initialized, havege_state);
  //@ ensures PRG_POSTCONDITION(havege_state_initialized, havege_state);
{
  return havege_random(havege_state, output, len);
}

/*@

#define GENERAL_PRE(PRINCIPAL) \
  [_]public_invar(nsl_pub) &*& \
  principal(PRINCIPAL, ?p_id) &*& \
  integer(socket, ?s) &*& \
    net_status(s, nil, ?port, connected) &*& \
  havege_state_initialized(havege_state) \

#define GENERAL_POST(PRINCIPAL) \
  [_]public_invar(nsl_pub) &*& \
  principal(PRINCIPAL, _) &*& \
  integer(socket, s) &*& \
    net_status(s, nil, port, connected) &*& \
  havege_state_initialized(havege_state) \

#define SENDER_INTER \
  crypto_chars(r_nonce, NONCE_SIZE, ?r_nonce_cs) &*& \
  ( \
    bad(sender) || bad(receiver) ? \
      [_]public_generated(nsl_pub)(r_nonce_cs) \
    : \
      [_]exists(?r_nonce_cg) &*& \
      r_nonce_cg == cg_random(receiver, _) &*& \
      r_nonce_cs == chars_for_cg(r_nonce_cg) &*& \
      cg_is_generated(r_nonce_cg) && \
      cg_info(r_nonce_cg) == int_pair(2, int_pair(sender, \
                                                  sender)) \
  )
  
@*/

void sender_msg1(int* socket, havege_state* havege_state, pk_context* r_context,
                 int sender, char* s_nonce)
  /*@ requires GENERAL_PRE(sender) &*&
               pk_context_with_key(r_context, pk_public,
                                   ?receiver, ?r_id, 8 * KEY_SIZE) &*&
               cryptogram(s_nonce, NONCE_SIZE, ?s_nonce_cs, ?s_nonce_cg) &*&
                 s_nonce_cg == cg_random(sender, _) &*&
                 cg_info(s_nonce_cg) == int_pair(1, receiver); @*/
  /*@ ensures  GENERAL_POST(sender) &*&
               pk_context_with_key(r_context, pk_public,
                                   receiver, r_id, 8 * KEY_SIZE) &*&
               cryptogram(s_nonce, NONCE_SIZE, s_nonce_cs, s_nonce_cg); @*/
{
  unsigned int size;
  char message[MSG1_SIZE];
  char encrypted[KEY_SIZE];
  
  // Construct the message
  //@ assert integer(&sender, ?sendr);
  //@ integer_to_chars(&sender);
  /*@ close optional_crypto_chars(false, (void*) &sender, 
                                  4, chars_of_int(sendr)); @*/
  memcpy(message, &sender, 4);
  /*@ open optional_crypto_chars(false, (void*) &sender, 
                                  4, chars_of_int(sendr)); @*/
  //@ open optional_crypto_chars(false, message, 4, chars_of_int(sendr));
  //@ chars_to_integer(&sender);
  //@ public_chars(message, 4, chars_of_int(sendr));
  //@ crypto_chars(message, 4, chars_of_int(sendr));
  //@ close optional_crypto_chars(true, s_nonce, NONCE_SIZE, s_nonce_cs);
  memcpy((void*) message + 4, s_nonce, NONCE_SIZE);
  //@ open optional_crypto_chars(true, s_nonce, NONCE_SIZE, s_nonce_cs);
  /*@ open optional_crypto_chars(true, (void*) message + 4, 
                                  NONCE_SIZE, s_nonce_cs); @*/
  //@ list<char> msg1 = append(chars_of_int(sendr), s_nonce_cs);
  //@ assert crypto_chars(message, MSG1_SIZE, msg1);  
  
   // Encrypt the message
  //@ close optional_crypto_chars(true, message, MSG1_SIZE, msg1);
  /*@ produce_function_pointer_chunk random_function(random_stub_nsl)
                    (havege_state_initialized)(state, out, len) { call(); } @*/
  //@ close random_state_predicate(havege_state_initialized); 
  if (pk_encrypt(r_context, message, MSG1_SIZE, encrypted, &size, 
                  KEY_SIZE, random_stub_nsl, havege_state) != 0)
    abort();
  //@ open optional_crypto_chars(true, message, MSG1_SIZE, msg1);
  //@ assert u_integer(&size, ?size_val);
  //@ assert cryptogram(encrypted, size_val, ?cs_enc, ?cg_enc);
  
  // Proof the message is public
  //@ take_append(4, chars_of_int(sendr), s_nonce_cs);
  //@ drop_append(4, chars_of_int(sendr), s_nonce_cs);
  //@ close nsl_pub_msg_sender(sendr);
  //@ leak nsl_pub_msg_sender(sendr);
  /*@ if (bad(sender) || bad(receiver))
      {
        assert crypto_chars(message, MSG1_SIZE, msg1);
        crypto_chars_split(message, 4);
        
        public_crypto_chars(message, 4, chars_of_int(sendr));
        assert chars(message, 4, chars_of_int(sendr));
        close nsl_pub(s_nonce_cg);
        leak nsl_pub(s_nonce_cg);
        close cryptogram((void*) message + 4, NONCE_SIZE, 
                          s_nonce_cs, s_nonce_cg);
        public_cryptogram((void*) message + 4, s_nonce_cg);
        assert chars((void*) message + 4, NONCE_SIZE, s_nonce_cs);
        chars_join(message);
        public_chars(message, MSG1_SIZE, msg1);
        crypto_chars(message, MSG1_SIZE, msg1);
      }
      else
      {
        close nsl_pub_msg1(sendr, receiver, s_nonce_cg);
      }
  @*/
  //@ close nsl_pub(cg_enc);
  //@ leak nsl_pub(cg_enc);
  //@ public_cryptogram(encrypted, cg_enc);

  // Send the message
  net_send(socket, encrypted, size);
  //@ close optional_crypto_chars(true, message, MSG1_SIZE, msg1);
  zeroize(message, MSG1_SIZE);
}

void sender_msg2(int* socket, havege_state* havege_state, pk_context* s_context, 
                 int sender, int receiver, char* s_nonce, char* r_nonce)
  /*@ requires GENERAL_PRE(sender) &*&
               pk_context_with_key(s_context, pk_private,
                                   sender, ?s_id, 8 * KEY_SIZE)  &*&
               cryptogram(s_nonce, NONCE_SIZE, ?s_nonce_cs, ?s_nonce_cg) &*&
                 s_nonce_cg == cg_random(sender, _) &*&
                 cg_info(s_nonce_cg) == int_pair(1, receiver) &*&
               chars(r_nonce, NONCE_SIZE, _); @*/
  /*@ ensures  GENERAL_POST(sender) &*&
               pk_context_with_key(s_context, pk_private,
                                   sender, s_id, 8 * KEY_SIZE) &*&
               cryptogram(s_nonce, NONCE_SIZE, s_nonce_cs, s_nonce_cg) &*&
               SENDER_INTER; @*/
{
  unsigned int size;
  char message[MSG2_SIZE];
  char encrypted[KEY_SIZE];
  
  // Receive the message
  net_recv(socket, encrypted, KEY_SIZE);
  //@ assert chars(encrypted, KEY_SIZE, ?enc_cs);
  
  // Decrypt the message
  //@ close optional_crypto_chars(false, encrypted, KEY_SIZE, enc_cs);
  /*@ produce_function_pointer_chunk random_function(random_stub_nsl)
                    (havege_state_initialized)(state, out, len) { call(); } @*/
  //@ close random_state_predicate(havege_state_initialized);
  if (pk_decrypt(s_context, encrypted, KEY_SIZE, message, 
                  &size, MSG2_SIZE, random_stub_nsl, havege_state) != 0)
    abort();
  if (size != MSG2_SIZE)
    abort();
  //@ open optional_crypto_chars(false, encrypted, KEY_SIZE, enc_cs);
  //@ assert u_integer(&size, MSG2_SIZE);  
  //@ assert crypto_chars(message, MSG2_SIZE, ?dec_cs);
  //@ assert [_]exists(?ent);
  //@ cryptogram enc_cg = cg_asym_encrypted(sender, s_id, dec_cs, ent);
  //@ assert enc_cs == chars_for_cg(enc_cg);
  //@ public_chars_extract(encrypted, enc_cg);
  //@ open [_]nsl_pub(enc_cg);
  
  // Interpret the message
  //@ crypto_chars_split(message, 4);
  //@ crypto_chars_split((void*) message + 4, NONCE_SIZE);
  //@ assert integer(&receiver, ?receivr);
  //@ integer_to_chars(&receiver);
  //@ public_chars((void*) &receiver, 4, chars_of_int(receivr));
  /*@ close optional_crypto_chars(false, (void*) &receiver, 
                                  4, chars_of_int(receivr)); @*/
  //@ close optional_crypto_chars(true, message, 4, _);
  if (memcmp(message, (void*) &receiver, 4) != 0) abort();
  //@ chars_to_integer(&receiver);
  //@ open optional_crypto_chars(true, message, 4, chars_of_int(receivr));
  
  //@ close optional_crypto_chars(true, (void*) message + 4, NONCE_SIZE, _);
  //@ close optional_crypto_chars(true, s_nonce, NONCE_SIZE, s_nonce_cs);
  if (memcmp((void*) message + 4, s_nonce, NONCE_SIZE) != 0) abort();
  //@ chars_to_integer(&receiver);
  //@ open optional_crypto_chars(true, (void*) message + 4, NONCE_SIZE, _);
  /*@ close optional_crypto_chars(true, (void*) message + 4 + NONCE_SIZE, 
                                  NONCE_SIZE, ?r_nonce_cs); @*/
  memcpy(r_nonce, (void*) message + 4 + NONCE_SIZE, NONCE_SIZE);
  //@ assert crypto_chars(r_nonce, NONCE_SIZE, r_nonce_cs);
  /*@ open optional_crypto_chars(true, (void*) message + 4 + NONCE_SIZE, 
                                 NONCE_SIZE, r_nonce_cs); @*/
  
  //@ append_assoc(chars_of_int(receivr), s_nonce_cs, r_nonce_cs);
  //@ take_append(4, chars_of_int(receivr), append(s_nonce_cs, r_nonce_cs));
  //@ drop_append(4, chars_of_int(receivr), append(s_nonce_cs, r_nonce_cs));
  //@ take_append(NONCE_SIZE, s_nonce_cs, r_nonce_cs);
  //@ drop_append(NONCE_SIZE, s_nonce_cs, r_nonce_cs);
        
  //@ assert [_]nsl_pub_msg_sender(?receiver2);
  /*@ if (bad(sender) || bad(receiver2))
      {
        crypto_chars_join(message);
        public_crypto_chars(message, MSG2_SIZE, dec_cs);
        chars_split(message, 4);
        chars_split((void*) message + 4, NONCE_SIZE);
        public_chars((void*) message + 4, NONCE_SIZE, s_nonce_cs);
        public_chars_extract((void*) message + 4, s_nonce_cg);
        open [_]nsl_pub(s_nonce_cg);
        assert bad(sender) || bad(receivr);
        public_chars((void*) message + 4 + NONCE_SIZE, NONCE_SIZE, r_nonce_cs);
        chars_join((void*) message + 4);
        crypto_chars((void*) message + 4, 2 * NONCE_SIZE, 
                     append(s_nonce_cs, r_nonce_cs));
      }
      else
      {
        public_crypto_chars(message, 4, chars_of_int(receivr));
        assert [_]nsl_pub_msg2(?p_instigator, sender, receiver2, 
                               ?s_nonce_cs2, ?r_nonce_cg);
        assert r_nonce_cg == cg_random(receiver2, _) ;
        list<char> r_nonce_cs2 = chars_for_cg(r_nonce_cg);
        take_append(4, chars_of_int(receiver2), 
                    append(s_nonce_cs2, r_nonce_cs2));
        drop_append(4, chars_of_int(receiver2),
                    append(s_nonce_cs2, r_nonce_cs2));
        take_append(NONCE_SIZE, s_nonce_cs2, r_nonce_cs2);
        drop_append(NONCE_SIZE, s_nonce_cs2, r_nonce_cs2);
        chars_of_int_injective(receiver2, receivr);
        assert receiver2 == receivr;
        assert s_nonce_cs2 == s_nonce_cs;
        assert r_nonce_cs2 == r_nonce_cs;
        assert cg_info(r_nonce_cg) == int_pair(2, int_pair(sender,
                                                           p_instigator));
        if (bad(p_instigator))
        {
          public_crypto_chars(s_nonce, NONCE_SIZE, s_nonce_cs);
          public_chars_extract(s_nonce, s_nonce_cg);
          open [_]nsl_pub(s_nonce_cg);
          assert false;
        }
        
        assert cg_info(r_nonce_cg) == int_pair(2, int_pair(sender, sender));
        close exists(r_nonce_cg);
        leak exists(r_nonce_cg);
      }
  @*/
  //@ close cryptogram(s_nonce, NONCE_SIZE, s_nonce_cs, s_nonce_cg);
  /*@ close optional_crypto_chars(true, (void*) message + 4, 2 * NONCE_SIZE, 
                                  append(s_nonce_cs, r_nonce_cs)); @*/
  zeroize((void*) message + 4, 2 * NONCE_SIZE);
  //@ chars_join(message);
}

void sender_msg3(int* socket, havege_state* havege_state, pk_context* r_context,
                 int sender, char* r_nonce)
  /*@ requires GENERAL_PRE(sender) &*&
               pk_context_with_key(r_context, pk_public,
                                   ?receiver, ?r_id, 8 * KEY_SIZE) &*&
               SENDER_INTER; @*/
  /*@ ensures  GENERAL_POST(sender) &*&
               pk_context_with_key(r_context, pk_public,
                                   receiver, r_id, 8 * KEY_SIZE) &*&
               crypto_chars(r_nonce, NONCE_SIZE, r_nonce_cs); @*/
{
  unsigned int size;
  char message[MSG3_SIZE];
  char encrypted[KEY_SIZE];
  
  // Construct the message
  //@ close optional_crypto_chars(true, r_nonce, NONCE_SIZE, r_nonce_cs);
  memcpy((void*) message, r_nonce, NONCE_SIZE);
  //@ open optional_crypto_chars(true, r_nonce, NONCE_SIZE, r_nonce_cs);
  
  // Encrypt the message
  /*@ produce_function_pointer_chunk random_function(random_stub_nsl)
                    (havege_state_initialized)(state, out, len) { call(); } @*/
  //@ close random_state_predicate(havege_state_initialized);
  if (pk_encrypt(r_context, message, MSG3_SIZE, encrypted, &size, 
                 KEY_SIZE, random_stub_nsl, havege_state) != 0)
    abort();
  //@ open optional_crypto_chars(true, message, MSG3_SIZE, r_nonce_cs);
  //@ assert u_integer(&size, ?size_val);
  //@ assert cryptogram(encrypted, size_val, ?cs_enc, ?cg_enc);
  
  // Proof the message is public
  //@ close nsl_pub_msg_sender(sender);
  //@ leak nsl_pub_msg_sender(sender);
  /*@ if (!bad(sender) && !bad(receiver))
      {
        assert [_]exists(?r_nonce_cg);
        close nsl_pub_msg3(sender, receiver, r_nonce_cg);
      }
  @*/
  //@ close nsl_pub(cg_enc);
  //@ leak nsl_pub(cg_enc);
  //@ public_cryptogram(encrypted, cg_enc);

  // Send the message
  net_send(socket, encrypted, size);
  //@ close optional_crypto_chars(true, message, MSG3_SIZE, r_nonce_cs);
  zeroize(message, MSG3_SIZE);
}

void sender(int sender, int receiver, 
            char *s_priv_key, char *r_pub_key,
            char *s_nonce, char *r_nonce)
/*@ requires [_]public_invar(nsl_pub) &*&
             principal(sender, _) &*&
             [?f1]cryptogram(s_priv_key, 8 * KEY_SIZE,
                             ?s_priv_key_cs, ?s_priv_key_cg) &*&
               s_priv_key_cg == cg_private_key(sender, ?s_id) &*&
             [?f2]cryptogram(r_pub_key, 8 * KEY_SIZE,
                             ?r_pub_key_cs, ?r_pub_key_cg) &*&
               r_pub_key_cg == cg_public_key(receiver, ?r_id) &*&
             chars(s_nonce, NONCE_SIZE, _) &*&
             chars(r_nonce, NONCE_SIZE, _); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(s_priv_key, 8 * KEY_SIZE,
                            s_priv_key_cs, s_priv_key_cg) &*&
             [f2]cryptogram(r_pub_key, 8 * KEY_SIZE,
                            r_pub_key_cs, r_pub_key_cg) &*&
             cryptogram(s_nonce, NONCE_SIZE, ?s_nonce_cs, ?s_nonce_cg) &*&
               s_nonce_cg == cg_random(sender, _) &*&
               cg_info(s_nonce_cg) == int_pair(1, receiver) &*&
             crypto_chars(r_nonce, NONCE_SIZE, ?r_nonce_cs) &*&
             bad(sender) || bad(receiver) ?
               [_]public_generated(nsl_pub)(r_nonce_cs)
             :
               [_]exists(?r_nonce_cg) &*&
               r_nonce_cg == cg_random(receiver, _) &*&
               cg_info(r_nonce_cg) == int_pair(2, int_pair(sender, sender));@*/
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
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  //@ close random_request(sender, int_pair(1, receiver), false);
  if (havege_random(&havege_state, s_nonce, NONCE_SIZE) != 0) abort();
  //@ assert cryptogram(s_nonce, NONCE_SIZE, ?cs_s_nonce, ?cg_s_nonce);
  
  sender_msg1(&socket, &havege_state, &r_context, sender, s_nonce);
  sender_msg2(&socket, &havege_state, &s_context, sender, receiver, 
              s_nonce, r_nonce);
  sender_msg3(&socket, &havege_state, &r_context, sender, r_nonce);
  
  //@ close cryptogram(s_nonce, NONCE_SIZE, cs_s_nonce, cg_s_nonce);
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

#define RECEIVER_INTER \
  ( \
    [_]nsl_pub_msg_sender(?p_instigator) &*& \
    bad(p_instigator) || bad(receiver) ? \
      [_]public_generated(nsl_pub)(s_nonce_cs) \
    : \
      [_]exists(?s_nonce_cg) &*& \
      sender == p_instigator &*& \
      s_nonce_cg == cg_random(sender, _) &*& \
      s_nonce_cs == chars_for_cg(s_nonce_cg) &*& \
      cg_is_generated(s_nonce_cg) && \
      cg_info(s_nonce_cg) == int_pair(1, receiver) \
  )

@*/

void receiver_msg1(int* socket, havege_state* havege_state, 
                   pk_context* r_context, int sender, int receiver, 
                   char* s_nonce)
  /*@ requires GENERAL_PRE(receiver) &*&
               pk_context_with_key(r_context, pk_private,
                                   receiver, ?r_id, 8 * KEY_SIZE)  &*&
               chars(s_nonce, NONCE_SIZE, _); @*/
  /*@ ensures  GENERAL_POST(receiver) &*&
               pk_context_with_key(r_context, pk_private,
                                   receiver, r_id, 8 * KEY_SIZE) &*&
               crypto_chars(s_nonce, NONCE_SIZE, ?s_nonce_cs) &*&
               RECEIVER_INTER; @*/
{
  unsigned int size;
  char message[MSG1_SIZE];
  char encrypted[KEY_SIZE];
  
  // Receive the message
  net_recv(socket, encrypted, KEY_SIZE);
  //@ assert chars(encrypted, KEY_SIZE, ?enc_cs);
  
  // Decrypt the message
  //@ close optional_crypto_chars(false, encrypted, KEY_SIZE, enc_cs);
  /*@ produce_function_pointer_chunk random_function(random_stub_nsl)
                    (havege_state_initialized)(state, out, len) { call(); } @*/
  //@ close random_state_predicate(havege_state_initialized);
  if (pk_decrypt(r_context, encrypted, KEY_SIZE, message, 
                  &size, MSG1_SIZE, random_stub_nsl, havege_state) != 0)
    abort();
  if (size != MSG1_SIZE)
    abort();
  //@ open optional_crypto_chars(false, encrypted, KEY_SIZE, enc_cs);
  //@ assert u_integer(&size, MSG1_SIZE);  
  //@ assert crypto_chars(message, MSG1_SIZE, ?dec_cs);
  //@ assert [_]exists(?ent);
  //@ cryptogram enc_cg = cg_asym_encrypted(receiver, r_id, dec_cs, ent);
  //@ assert enc_cs == chars_for_cg(enc_cg);
  //@ public_chars_extract(encrypted, enc_cg);
  //@ open [_]nsl_pub(enc_cg);
  
  // Interpret the message
  //@ assert [_]nsl_pub_msg_sender(?p_instigator);
  /*@ if (bad(p_instigator) || bad(receiver))
      {
        public_crypto_chars(message, MSG1_SIZE, dec_cs);
      }
      else
      {
        crypto_chars_split(message, 4);
        assert crypto_chars(message, 4, ?rcvr_cs);
        public_crypto_chars(message, 4, rcvr_cs);
      }
  @*/
  //@ assert chars(message, 4, _);
  //@ assert integer(&sender, ?sendr);
  //@ integer_to_chars(&sender);
  /*@ close optional_crypto_chars(false, (void*) &sender, 
                                  4, chars_of_int(sendr)); @*/
  //@ close optional_crypto_chars(false, message, 4, _); 
  if (memcmp(message, (void*) &sender, 4) != 0) abort();
  //@ open optional_crypto_chars(false, message, 4, _);
  //@ chars_to_integer(&sender);
  //@ assert chars(message, 4, _);
  /*@ if (bad(p_instigator) || bad(receiver))
      {
        assert chars((void*) message + 4, NONCE_SIZE, ?s_nonce_cs);
        public_chars((void*) message + 4, NONCE_SIZE, s_nonce_cs);
        crypto_chars((void*) message + 4, NONCE_SIZE, s_nonce_cs);
      }
      else
      {
        assert [_]nsl_pub_msg1(p_instigator, receiver, ?s_nonce_cg);
        assert s_nonce_cg == cg_random(p_instigator, _);
        list<char> s_nonce_cs = chars_for_cg(s_nonce_cg);
        assert dec_cs == append(chars_of_int(p_instigator), s_nonce_cs);
        take_append(4, chars_of_int(p_instigator), s_nonce_cs);
        drop_append(4, chars_of_int(p_instigator), s_nonce_cs);
        assert chars_of_int(p_instigator) == chars_of_int(sendr);
        chars_of_int_injective(p_instigator, sendr);
        assert p_instigator == sendr;
        assert cg_info(s_nonce_cg) == int_pair(1, receiver);
        assert crypto_chars((void*) message + 4, NONCE_SIZE, _);
        close exists(s_nonce_cg);
        leak exists(s_nonce_cg);
      }
  @*/
  //@ close optional_crypto_chars(true, (void*) message + 4, NONCE_SIZE, _);
  memcpy(s_nonce, (void*) message + 4, NONCE_SIZE);
  //@ assert crypto_chars(s_nonce, NONCE_SIZE, ?s_nonce_cs);
  zeroize((void*) message + 4, NONCE_SIZE);
}

void receiver_msg2(int* socket, havege_state* havege_state, 
                   pk_context* s_context, int receiver, 
                   char* s_nonce, char* r_nonce)
  /*@ requires GENERAL_PRE(receiver) &*&
               pk_context_with_key(s_context, pk_public,
                                   ?sender, ?s_id, 8 * KEY_SIZE) &*&
               crypto_chars(s_nonce, NONCE_SIZE, ?s_nonce_cs) &*&
               RECEIVER_INTER &*&
               cryptogram(r_nonce, NONCE_SIZE, ?r_nonce_cs, ?r_nonce_cg) &*&
                 r_nonce_cg == cg_random(receiver, _) &*&
                 cg_info(r_nonce_cg) == int_pair(2, int_pair(sender,
                                                             p_instigator)); @*/
  /*@ ensures  GENERAL_POST(receiver) &*&
               pk_context_with_key(s_context, pk_public,
                                   sender, s_id, 8 * KEY_SIZE) &*&
               crypto_chars(s_nonce, NONCE_SIZE, s_nonce_cs) &*&
               cryptogram(r_nonce, NONCE_SIZE, r_nonce_cs, r_nonce_cg); @*/
{
  unsigned int size;
  char message[MSG2_SIZE];
  char encrypted[KEY_SIZE];
  
  // Construct the message
  //@ assert integer(&receiver, ?receivr);
  //@ integer_to_chars(&receiver);
  /*@ close optional_crypto_chars(false, (void*) &receiver, 
                                  4, chars_of_int(receivr)); @*/
  memcpy(message, &receiver, 4);
  /*@ open optional_crypto_chars(false, (void*) &receiver, 
                                  4, chars_of_int(receivr)); @*/
  //@ open optional_crypto_chars(false, message, 4, chars_of_int(receivr));
  //@ chars_to_integer(&receiver);
  //@ public_chars(message, 4, chars_of_int(receivr));
  //@ crypto_chars(message, 4, chars_of_int(receivr));
  //@ close optional_crypto_chars(true, s_nonce, NONCE_SIZE, _);
  memcpy((void*) message + 4, s_nonce, NONCE_SIZE);
  //@ open optional_crypto_chars(true, s_nonce, NONCE_SIZE, _);
  /*@ open optional_crypto_chars(true, (void*) message + 4, 
                                  NONCE_SIZE, s_nonce_cs); @*/
  //@ close optional_crypto_chars(true, r_nonce, NONCE_SIZE, _);
  memcpy((void*) message + 4 + NONCE_SIZE, r_nonce, NONCE_SIZE);
  //@ open optional_crypto_chars(true, r_nonce, NONCE_SIZE, _);
  /*@ open optional_crypto_chars(true, (void*) message + 4 + NONCE_SIZE, 
                                  NONCE_SIZE, r_nonce_cs); @*/
  //@ crypto_chars_join(message);
  /*@ list<char> msg2 = append(chars_of_int(receivr), 
                               append(s_nonce_cs, r_nonce_cs)); @*/
  //@ append_assoc(chars_of_int(receivr), s_nonce_cs, r_nonce_cs);
  //@ assert crypto_chars(message, MSG2_SIZE, msg2);
  
  // Encrypt the message
  //@ close optional_crypto_chars(true, message, MSG2_SIZE, msg2);
  /*@ produce_function_pointer_chunk random_function(random_stub_nsl)
                    (havege_state_initialized)(state, out, len) { call(); } @*/
  //@ close random_state_predicate(havege_state_initialized); 
  if (pk_encrypt(s_context, message, MSG2_SIZE, encrypted, &size, 
                  KEY_SIZE, random_stub_nsl, havege_state) != 0)
    abort();
  //@ open optional_crypto_chars(true, message, MSG2_SIZE, msg2);
  //@ assert u_integer(&size, ?size_val);
  //@ assert cryptogram(encrypted, size_val, ?cs_enc, ?cg_enc);
  
  // Proof the message is public
  //@ take_append(4, chars_of_int(receivr), append(s_nonce_cs, r_nonce_cs));
  //@ drop_append(4, chars_of_int(receivr), append(s_nonce_cs, r_nonce_cs));
  //@ take_append(NONCE_SIZE, s_nonce_cs, r_nonce_cs);
  //@ drop_append(NONCE_SIZE, s_nonce_cs, r_nonce_cs);
  /*@ if (bad(sender) || bad(receiver))
      {
        assert crypto_chars(message, MSG2_SIZE, msg2);
        crypto_chars_split(message, 4);
        crypto_chars_split((void*) message + 4, NONCE_SIZE);
        public_crypto_chars((void*) message, 4, chars_of_int(receivr));
        public_crypto_chars((void*) message + 4, NONCE_SIZE, s_nonce_cs);
        close nsl_pub(r_nonce_cg);
        leak nsl_pub(r_nonce_cg);
        close cryptogram((void*) message + 4 + NONCE_SIZE, NONCE_SIZE, 
                         r_nonce_cs, r_nonce_cg);
        public_cryptogram((void*) message + 4 + NONCE_SIZE, r_nonce_cg);
        assert chars((void*) message + 4 + NONCE_SIZE, NONCE_SIZE, r_nonce_cs);
        chars_join((void*) message + 4);
        chars_join(message);
        public_chars(message, MSG2_SIZE, msg2);
        crypto_chars(message, MSG2_SIZE, msg2);
      }
      else
      {
        close nsl_pub_msg2(p_instigator, sender, receiver, 
                           s_nonce_cs, r_nonce_cg);
      }
  @*/
  //@ close nsl_pub_msg_sender(receivr);
  //@ leak nsl_pub_msg_sender(receivr);
  //@ close nsl_pub(cg_enc);
  //@ leak nsl_pub(cg_enc);
  //@ public_cryptogram(encrypted, cg_enc);
  
  // Send the message
  net_send(socket, encrypted, size);
  //@ close optional_crypto_chars(true, message, MSG2_SIZE, msg2);
  zeroize(message, MSG2_SIZE);
}

void receiver_msg3(int* socket, havege_state* havege_state, 
                   pk_context* r_context, int sender, int receiver, 
                   char* s_nonce, char* r_nonce)
  /*@ requires GENERAL_PRE(receiver) &*&
               pk_context_with_key(r_context, pk_private,
                                   receiver, ?r_id, 8 * KEY_SIZE)  &*&
               crypto_chars(s_nonce, NONCE_SIZE, ?s_nonce_cs) &*&
                 RECEIVER_INTER &*&  
               cryptogram(r_nonce, NONCE_SIZE, ?r_nonce_cs, ?r_nonce_cg) &*&
                 r_nonce_cg == cg_random(receiver, _) &*&
                 cg_info(r_nonce_cg) == 
                                int_pair(2, int_pair(sender, p_instigator)); @*/
  /*@ ensures  GENERAL_POST(receiver) &*&
               pk_context_with_key(r_context, pk_private,
                                   receiver, r_id, 8 * KEY_SIZE) &*&
               crypto_chars(s_nonce, NONCE_SIZE, s_nonce_cs) &*&
               cryptogram(r_nonce, NONCE_SIZE, r_nonce_cs, r_nonce_cg) &*&
               collision_in_run || bad(sender) || bad(receiver) || 
                 sender == p_instigator; @*/
{
  unsigned int size;
  char message[MSG3_SIZE];
  char encrypted[KEY_SIZE];
  
  // Receive the message
  net_recv(socket, encrypted, KEY_SIZE);
  //@ assert chars(encrypted, KEY_SIZE, ?enc_cs);
  
  // Decrypt the message
  //@ close optional_crypto_chars(false, encrypted, KEY_SIZE, enc_cs);
  /*@ produce_function_pointer_chunk random_function(random_stub_nsl)
                    (havege_state_initialized)(state, out, len) { call(); } @*/
  //@ close random_state_predicate(havege_state_initialized);
  if (pk_decrypt(r_context, encrypted, KEY_SIZE, message, 
                  &size, MSG3_SIZE, random_stub_nsl, havege_state) != 0)
    abort();
  if (size != MSG3_SIZE)
    abort();
  //@ open optional_crypto_chars(false, encrypted, KEY_SIZE, enc_cs);
  //@ assert u_integer(&size, MSG3_SIZE);  
  //@ assert crypto_chars(message, MSG3_SIZE, ?dec_cs);
  //@ assert [_]exists(?ent);
  //@ cryptogram enc_cg = cg_asym_encrypted(receiver, r_id, dec_cs, ent);
  //@ assert enc_cs == chars_for_cg(enc_cg);
  //@ public_chars_extract(encrypted, enc_cg);
  
  // Interpret the message
  //@ close optional_crypto_chars(true, (void*) message, NONCE_SIZE, _);
  //@ close optional_crypto_chars(true, r_nonce, NONCE_SIZE, r_nonce_cs);
  if (memcmp((void*) message, r_nonce, NONCE_SIZE) != 0) abort();
  
  /*@ if (!bad(sender) && !bad(receiver))
      {
        open [_]nsl_pub(enc_cg);
        assert [_]nsl_pub_msg_sender(?sender2);
        if (bad(sender2))
        {
          public_crypto_chars(r_nonce, NONCE_SIZE, r_nonce_cs);
          public_chars_extract(r_nonce, r_nonce_cg);
          open [_]nsl_pub(r_nonce_cg);
          assert false;
        }
        else
        {
          if (!collision_in_run && bad(p_instigator))
          {
            assert [_]nsl_pub_msg3(sender2, receiver, ?r_nonce_cg2);
            int p1 = int_pair(sender, p_instigator);
            int p2 = int_pair(sender2, sender2);
            assert cg_info(r_nonce_cg) == int_pair(2, p1);
            assert cg_info(r_nonce_cg2) == int_pair(2, p2);
            chars_for_cg_inj(r_nonce_cg, r_nonce_cg2);
            assert r_nonce_cg == r_nonce_cg2;
            assert int_pair(2, p1) == int_pair(2, p2);
            int_right_int_pair(2, p1);
            int_right_int_pair(2, p2);
            assert p1 == p2;
            int_right_int_pair(sender, p_instigator);
            int_left_int_pair(sender, p_instigator);
            int_right_int_pair(sender2, sender2);
            int_left_int_pair(sender2, sender2);
            assert false;
          }
        }
      }
  @*/
  zeroize(message, MSG3_SIZE);
  //@ close cryptogram(r_nonce, NONCE_SIZE, r_nonce_cs, r_nonce_cg);
}

void receiver(int sender, int receiver, 
              char *s_pub_key, char *r_priv_key,
              char *s_nonce, char *r_nonce)
/*@ requires [_]public_invar(nsl_pub) &*&
             principal(receiver, _) &*&
             [?f1]cryptogram(s_pub_key, 8 * KEY_SIZE,
                             ?s_pub_key_cs, ?s_pub_key_cg) &*&
               s_pub_key_cg == cg_public_key(sender, ?s_id) &*&
             [?f2]cryptogram(r_priv_key, 8 * KEY_SIZE, 
                             ?r_priv_key_cs, ?r_priv_key_cg) &*&
               r_priv_key_cg == cg_private_key(receiver, ?r_id) &*&
             chars(s_nonce, NONCE_SIZE, _) &*&
             chars(r_nonce, NONCE_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(s_pub_key, 8 * KEY_SIZE,
                            s_pub_key_cs, s_pub_key_cg) &*&
             [f2]cryptogram(r_priv_key, 8 * KEY_SIZE,
                            r_priv_key_cs, r_priv_key_cg) &*&
             crypto_chars(s_nonce, NONCE_SIZE, ?s_nonce_cs) &*&
             cryptogram(r_nonce, NONCE_SIZE, ?r_nonce_cs, ?r_nonce_cg) &*&
               r_nonce_cg == cg_random(receiver, _) &*&
             (
               collision_in_run || bad(sender) || bad(receiver) ?
                 true
               :
                 [_]exists(?s_nonce_cg) &*&
                 s_nonce_cs == chars_for_cg(s_nonce_cg) &*&
                 s_nonce_cg == cg_random(sender, _) &*&
                 cg_info(s_nonce_cg) == int_pair(1, receiver) &*&
                 cg_info(r_nonce_cg) == int_pair(2, int_pair(sender, sender))   
             ); @*/
{
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
  
  receiver_msg1(&socket2, &havege_state, &r_context, sender, receiver, s_nonce);
  
  //@ assert [_]nsl_pub_msg_sender(?p_instigator);
  /*@ close random_request(receiver, int_pair(2, int_pair(sender,
                                                   p_instigator)), false); @*/
  if (havege_random(&havege_state, r_nonce, NONCE_SIZE) != 0) abort();
  
  receiver_msg2(&socket2, &havege_state, &s_context, receiver, 
                s_nonce, r_nonce);
  receiver_msg3(&socket2, &havege_state, &r_context, sender, receiver, 
                s_nonce, r_nonce);
  
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
