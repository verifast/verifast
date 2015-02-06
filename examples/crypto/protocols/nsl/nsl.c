#include "nsl.h"
#include "stdlib.h"

#include <stdio.h>

#define SERVER_PORT1 123123
#define SERVER_PORT2 234234
#define RECEIVER_PORT 345345
  
void server(char server, struct item *KS_PRIVATE)
  /*@ requires [?f0]world(nsl_pub) &*&
               generated_values(server, _) &*&
               !bad(server) &*&
               item(KS_PRIVATE, ?ksp, nsl_pub) &*& 
                 ksp == private_key_item(server, 1); @*/
  /*@ ensures  [f0]world(nsl_pub) &*&
               generated_values(server, _) &*&
               item(KS_PRIVATE, ksp, nsl_pub); @*/
{
  struct network_status *net_stat_in1  = network_bind_and_accept(SERVER_PORT1);
  struct item *A = network_receive(net_stat_in1);
  check_is_data(A);
  //@ assert item(A, ?a, nsl_pub);
  //@ get_info_for_item(a);
  //@ close nsl_pub(a);
  //@ leak nsl_pub(a);
  char A_data = item_get_data_as_char(A);
  struct item *KA = get_public_key(A_data);
  //@ assert item(KA, ?ka, nsl_pub);
  //@ get_info_for_item(ka);
  //@ close nsl_pub(ka);
  //@ leak nsl_pub(ka);
  struct item *A_pair = create_pair(A, KA);
  //@ assert item(A_pair, ?a_pair, nsl_pub);
  //@ get_info_for_item(a_pair);
  //@ close nsl_pub(a_pair);
  //@ leak nsl_pub(a_pair);
  struct item * A_hash = create_hash(A_pair);
  struct item *A_sign = asymmetric_signature(KS_PRIVATE, A_hash);
  //@ assert item(A_sign, ?a_sign, nsl_pub);
  //@ get_info_for_item(a_sign);
  //@ close message_tag(a_sign)(21);
  //@ leak message_tag(a_sign)(21);
  //@ close nsl_pub(a_sign);
  //@ leak nsl_pub(a_sign);
  struct item *A_msg = create_pair(A_pair, A_sign);
  //@ assert item(A_msg, ?a_msg, nsl_pub);
  //@ get_info_for_item(a_msg);
  //@ close nsl_pub(a_msg);
  //@ leak nsl_pub(a_msg);
  network_send(net_stat_in1, A_msg);
  network_disconnect(net_stat_in1);
  
  struct network_status *net_stat_in2  = network_bind_and_accept(SERVER_PORT2);
  struct item *B = network_receive(net_stat_in2);
  check_is_data(B);
  //@ assert item(B, ?b, nsl_pub);
  //@ get_info_for_item(b);
  //@ close nsl_pub(b);
  //@ leak nsl_pub(b);
  char B_data = item_get_data_as_char(B);
  struct item *KB = get_public_key(B_data);
  //@ assert item(KB, ?kb, nsl_pub);
  //@ get_info_for_item(kb);
  //@ close nsl_pub(kb);
  //@ leak nsl_pub(kb);
  struct item *B_pair = create_pair(B, KB);
  //@ assert item(B_pair, ?b_pair, nsl_pub);
  //@ get_info_for_item(b_pair);
  //@ close nsl_pub(b_pair);
  //@ leak nsl_pub(b_pair);
  struct item * B_hash = create_hash(B_pair);
  struct item *B_sign = asymmetric_signature(KS_PRIVATE, B_hash);
  //@ assert item(B_sign, ?b_sign, nsl_pub);
  //@ get_info_for_item(b_sign);
  //@ close message_tag(b_sign)(21);
  //@ leak message_tag(b_sign)(21);
  //@ close nsl_pub(b_sign);
  //@ leak nsl_pub(b_sign);
  struct item *B_msg = create_pair(B_pair, B_sign);
  //@ assert item(B_msg, ?b_msg, nsl_pub);
  //@ get_info_for_item(b_msg);
  //@ close nsl_pub(b_msg);
  //@ leak nsl_pub(b_msg);
  network_send(net_stat_in2, B_msg);
  network_disconnect(net_stat_in2);
  
  item_free(A);
  item_free(KA);
  item_free(A_pair);
  item_free(A_hash);
  item_free(A_sign);
  item_free(A_msg);
  item_free(B);
  item_free(KB);
  item_free(B_pair);
  item_free(B_hash);
  item_free(B_sign);
  item_free(B_msg);
}

struct item* retreive_public_key(char principal, struct item *KS, int port)
  /*@ requires [?f0]world(nsl_pub) &*&
               item(KS, ?ks, nsl_pub) &*&
                 ks == public_key_item(?server, 1) &*& !bad(server); @*/
  /*@ ensures  [f0]world(nsl_pub) &*&
               item(KS, ks, nsl_pub) &*&
               item(result, ?k, nsl_pub) &*&
               collision_in_run() ? 
                 true 
               : 
                 k == public_key_item(principal, 1); @*/
{
  struct network_status *net_stat = network_connect("localhost", port);
  //@ item P_data = data_item(cons(principal, nil));
  struct item *P = create_data_item_from_char(principal);
  //@ assert item(P, P_data, nsl_pub);
  //@ get_info_for_item(P_data);
  //@ close nsl_pub(P_data);
  //@ leak nsl_pub(P_data);
  //@ get_info_for_item(P_data);
  network_send(net_stat, P);
  
  struct item* msg = network_receive(net_stat);
  //@ assert item(msg, ?msg_, nsl_pub);
  struct item* msg_1 = pair_get_first(msg);
  //@ assert item(msg_1, ?msg_1_, nsl_pub);
  struct item* msg_2 = pair_get_second(msg);
  //@ assert item(msg_2, ?msg_2_, nsl_pub);
  struct item *hash = create_hash(msg_1);
  asymmetric_signature_verify(KS, hash, msg_2);
  struct item* P2 = pair_get_first(msg_1);
  if (!item_equals(P, P2)) abort();
  struct item* K = pair_get_second(msg_1);
  check_is_public_key(K);
  //@ assert item(K, ?K_, nsl_pub);
  
  /*@ if (!collision_in_run())
      {
        open [_]nsl_pub(msg_);
        assert msg_ == pair_item(msg_1_, msg_2_);
        open [_]nsl_pub(msg_2_);
        assert [_]message_tag(msg_2_)(?tag) &*& tag == 21;
        assert msg_2_ == asymmetric_signature_item(server, 1, some(?pay_), _);
        assert pay_ == hash_item(some(msg_1_));
        assert msg_1_ == pair_item(P_data, K_);
        assert K_ == public_key_item(principal, 1);
      }
  @*/
  
  item_free(P);
  item_free(msg);
  item_free(hash);
  item_free(msg_1);
  item_free(msg_2);
  item_free(P2);
  network_disconnect(net_stat);
  
  return K;
}

void sender(char sender, char receiver, char server,
            struct item *KA_PRIVATE, struct item *KS,
            struct item **NA, struct item **NB)
  /*@ requires [?f0]world(nsl_pub) &*&
               generated_values(sender, _) &*& 
               !bad(sender) &*& !bad(receiver) &*& !bad(server) &*&
               item(KA_PRIVATE, ?kap, nsl_pub) &*& 
                 kap == private_key_item(sender, 1) &*&
               item(KS, ?ks, nsl_pub) &*&
                 ks == public_key_item(server, 1) &*&
               pointer(NA, _) &*& pointer(NB, _); @*/
  /*@ ensures  [f0]world(nsl_pub) &*&
               generated_values(sender, _) &*&
               item(KA_PRIVATE, kap, nsl_pub) &*& 
               item(KS, ks, nsl_pub) &*&
               pointer(NA, ?nap) &*& pointer(NB, ?nbp) &*&
               item(nap, ?na, nsl_pub) &*&
                 [_]info_for_item(na, ?i_na) &*&
               item(nbp, ?nb, nsl_pub) &*&
                 [_]info_for_item(nb, ?i_nb) &*&
               collision_in_run() ?
                 true
               :
                 // Secrecy of NA
                 na == nonce_item(sender, _, 0) &*&
                 i_na == int_pair(1, receiver) &*&
                 is_not_public(_, nsl_pub, na, i_na) &*&
                 // Secrecy of NB
                 nb == nonce_item(receiver, _, 0) &*&
                 i_nb == int_pair(2, int_pair(sender, receiver)) &*&
                 is_not_public(_, nsl_pub, nb, i_nb); @*/
{
  struct item *KB = retreive_public_key(receiver, KS, SERVER_PORT1);
  check_is_public_key(KB);
  struct network_status *net_stat = network_connect("localhost", RECEIVER_PORT);
  //@ item A_ = data_item(cons(sender, nil));
  //@ item B_ = data_item(cons(receiver, nil));
  //@ assert character(&sender, ?send);
  //@ assert character(&receiver, ?recv);
  struct item *A = create_data_item(&sender, 1); 
  struct item *B = create_data_item(&receiver, 1); 
  //@ open chars(&sender, _, cons(send, nil));
  //@ open chars(&receiver, _, cons(recv, nil));
  //@ assert item(A, A_, nsl_pub);
  //@ assert item(B, B_, nsl_pub);
  
  //0. A -> B. A
  //@ get_info_for_item(A_);
  //@ close nsl_pub(A_);
  //@ leak nsl_pub(A_);
  network_send(net_stat, A);
  
  //1. A -> B. {A,NA}_K(B)
  struct item *NAP;
  {
    //@ close nonce_request(sender, int_pair(1, receiver));
    NAP = create_nonce();
    //@ assert item(NAP, ?NA_, nsl_pub);
    //@ assert [_]info_for_item(NA_, ?info_NA);
    struct item *i1 = create_pair(A, NAP); // (A, NA)
    //@ assert item(i1, ?i1_, nsl_pub);
    struct item *msg = asymmetric_authenticated_encryption(receiver, KB, 
                                                           KA_PRIVATE, i1);
    //@ assert item(msg, ?msg_, nsl_pub);
    
    /*@ if (!collision_in_run())
        {
          assert i1_ == pair_item(A_, NA_);
          assert msg_ == pair_item(?enc_, ?sig_);
          assert enc_ == asymmetric_encrypted_item(recv, 1, some(i1_), _);
          assert sig_ == asymmetric_signature_item(send, 1, some(?msg_id_), _);
          assert msg_id_ == pair_item(B_, hash_item(some(enc_)));
          get_info_for_item(enc_);
          close message_tag(enc_)(12);
          leak message_tag(enc_)(12);
          close nsl_pub(enc_);
          leak nsl_pub(enc_);
          close message_tag(sig_)(22);
          leak message_tag(sig_)(22);
          get_info_for_item(sig_);
          close nsl_pub(sig_);
          leak nsl_pub(sig_);
          {
            // Secrecy of NA
            lemma void not_public_na()
              requires  [_]nsl_pub(NA_) &*& [_]info_for_item(NA_, info_NA);
              ensures   false;
            { 
              open [_]nsl_pub(NA_);
              assert [_]info_for_item(NA_, ?info_NA2);
              info_for_item_is_function(NA_, info_NA, info_NA2);
              assert false;
            }
            produce_lemma_function_pointer_chunk(not_public_na) : 
                                not_public(nsl_pub, NA_, info_NA)() { call(); };
          }
        }
    @*/
    //@ get_info_for_item(msg_);
    //@ close nsl_pub(msg_);
    //@ leak nsl_pub(msg_);
    network_send(net_stat, msg);
    item_free(msg);
    item_free(i1);
  }
  
  //@ assert item(NAP, ?NA_, nsl_pub);
  
  // 2. B -> A. {B,NA,NB}_K(A)
  struct item *NBP;
  {
    struct item* msg = network_receive(net_stat);
    //@ assert item(msg, ?msg_, nsl_pub);
    struct item* pay =
                    asymmetric_authenticated_decryption(sender, KB, 
                                                        KA_PRIVATE, msg);
    struct item *i1 = pair_get_first(pay);
      if (!item_equals(B, i1)) abort ();
    //@ assert item(i1, ?i1_, nsl_pub);
    struct item *i2 = pair_get_second(pay);
    //@ assert item(i2, ?i2_, nsl_pub);
    struct item *i3 = pair_get_first(i2);
      if (!item_equals(NAP, i3)) abort ();
    //@ assert item(i3, ?i3_, nsl_pub);
    NBP = pair_get_second(i2);
      check_is_nonce(NBP);
    //@ assert item(NBP, ?NB_, nsl_pub);

    /*@ if (!collision_in_run())
        {
          assert msg_ == pair_item(?enc_, ?sig_);
          open [_]nsl_pub(msg_);
          open [_]nsl_pub(sig_);
          assert enc_ == asymmetric_encrypted_item(send, 1, some(?pay1_), _);
          assert sig_ == asymmetric_signature_item(recv, 1, some(?msg_id_), _);
          assert msg_id_ == pair_item(A_, ?hash_);
          assert hash_ == hash_item(some(enc_));
          msg_ == pair_item(B_, i2_);
          i2_ == pair_item(NA_, NB_);
          assert NB_ == nonce_item(recv, _, 0);
          assert [_]info_for_item(NB_, ?info_NB);
          assert info_NB == int_pair(2, int_pair(sender, receiver));
          {          
            // Secrecy of NB
            lemma void not_public_nb()
              requires  [_]nsl_pub(NB_) &*& [_]info_for_item(NB_, info_NB);
              ensures   false;
            { 
              open [_]nsl_pub(NB_);
              assert [_]info_for_item(NB_, ?info_NB2);
              info_for_item_is_function(NB_, info_NB, info_NB2);
              assert false;
            }
            produce_lemma_function_pointer_chunk(not_public_nb) :
                                not_public(nsl_pub, NB_, info_NB)() { call(); };
          }
        }
        else
        {
          get_info_for_item(NB_);
        }
    @*/
    item_free(msg);
    item_free(pay);
    item_free(i1);
    item_free(i2);
    item_free(i3);
  }

  //@ assert item(NBP, ?NB_, nsl_pub);
  
  //3. A -> B. {NB}_K(B)
  {
    struct item *msg = asymmetric_authenticated_encryption(receiver, KB, 
                                                           KA_PRIVATE, NBP);
    //@ assert item(msg, ?msg_, nsl_pub);
    
    /*@ if (!collision_in_run())
        {
          assert msg_ == pair_item(?enc_, ?sig_);
          assert enc_ == asymmetric_encrypted_item(recv, 1, some(NB_), _);
          assert sig_ == asymmetric_signature_item(send, 1, some(?msg_id_), _);
          assert msg_id_ == pair_item(B_, hash_item(some(enc_)));
          get_info_for_item(enc_);
          close message_tag(enc_)(14);
          leak message_tag(enc_)(14);
          close nsl_pub(enc_);
          leak nsl_pub(enc_);
          close message_tag(sig_)(24);
          leak message_tag(sig_)(24);
          get_info_for_item(sig_);
          close nsl_pub(sig_);
          leak nsl_pub(sig_);
        }
    @*/
    //@ get_info_for_item(msg_);
    //@ close nsl_pub(msg_);
    //@ leak nsl_pub(msg_);
    network_send(net_stat, msg);
    item_free(msg);
  }
  
  item_free(A);
  item_free(B);
  item_free(KB);
  
  *NA = NAP;
  *NB = NBP;
  
  network_disconnect(net_stat);
}

int receiver(char receiver, char server, 
              struct item *KB_PRIVATE, struct item *KS,
              struct item **NA, struct item **NB)
  /*@ requires [?f0]world(nsl_pub) &*&
               generated_values(receiver, _) &*& 
               !bad(receiver) &*& !bad(server) &*&
               item(KB_PRIVATE, ?kbp, nsl_pub) &*&
                 kbp == private_key_item(receiver, 1) &*&
               item(KS, ?ks, nsl_pub) &*&
                 ks == public_key_item(server, 1) &*&
               pointer(NA, _) &*& pointer(NB, _); @*/
  /*@ ensures  [f0]world(nsl_pub) &*&
               generated_values(receiver, _) &*& !bad(receiver) &*&
               item(KB_PRIVATE, kbp, nsl_pub) &*&
               item(KS, ks, nsl_pub)&*&
               pointer(NA, ?nap) &*& pointer(NB, ?nbp) &*&
               item(nbp, ?nb, nsl_pub) &*&
                 [_]info_for_item(nb, ?i_nb) &*&
               item(nap, ?na, nsl_pub) &*&
                 [_]info_for_item(na, ?i_na) &*&
               collision_in_run() || bad(result) ?
                 true
               :
                 // Secrecy of NB
                 nb == nonce_item(receiver, _, 0) &*&
                 i_nb == int_pair(2, int_pair(result, receiver)) &*&
                 is_not_public(_, nsl_pub, nb, i_nb) &*&
                 // Secrecy of NA
                 na == nonce_item(result, _, 0) &*&
                 i_na == int_pair(1, receiver) &*&
                 is_not_public(_, nsl_pub, na, i_na); @*/
{
  struct network_status *net_stat = network_bind_and_accept(RECEIVER_PORT);
  //@ item B_ = data_item(cons(receiver, nil));
  //@ assert character(&receiver, ?recv);
  struct item *B = create_data_item(&receiver, 1); 
  //@ open chars(&receiver, _, cons(recv, nil));
  //@ assert item(B, B_, nsl_pub);
  
  //0. A -> B. A
  struct item *A = network_receive(net_stat);
  check_is_data(A);
  //@ assert item(A, ?A_, nsl_pub);
  char sender = item_get_data_as_char(A);
  struct item *KA = retreive_public_key(sender, KS, SERVER_PORT2);
  check_is_public_key(KA);
  //@ assert item(KA, ?KA_, nsl_pub);
  //@ assert collision_in_run() ? true : KA_ == public_key_item(sender, 1);
  
  //1. A -> B. {A,NA}_K(B)
  struct item *NAP = 0;
  {
    struct item* msg = network_receive(net_stat);
    //@ assert item(msg, ?msg_, nsl_pub);
    struct item* pay =
                    asymmetric_authenticated_decryption(receiver, KA, 
                                                        KB_PRIVATE, msg);
    //@ assert item(pay, ?pay_, nsl_pub);
    struct item *i1 = pair_get_first(pay);
      if (!item_equals(A, i1)) abort();
    NAP = pair_get_second(pay);
      check_is_nonce(NAP);
    //@ assert item(NAP, ?NA_, nsl_pub);
    //@ assert NA_ == nonce_item(?NA_creator, _, _);
    /*@ if (!collision_in_run())
        {
          assert A_ == data_item(cons(sender, nil));
          assert pay_ == pair_item(A_, NA_);
          
          assert msg_ == pair_item(?enc_, ?sig_);
          assert enc_ == asymmetric_encrypted_item(?p1, ?c1, ?pay1, _);
          assert sig_ == asymmetric_signature_item(sender, 1, some(?msg_id_), _);
          assert msg_id_ == pair_item(B_, ?hash_);
          assert hash_ == hash_item(some(enc_));
          
          open [_]nsl_pub(msg_);
          open [_]nsl_pub(sig_);
          if (bad(sender))
          {
            if (p1 == receiver && c1 == 1)
            {
              assert some(pay_) == pay1;
              open [_]nsl_pub(msg_id_);
              open [_]nsl_pub(hash_);
              open [_]nsl_pub(enc_);
              assert [_]message_tag(enc_)(?tag);
              if (tag == 10)
              {
                open [_]nsl_pub(pay_);
              }
              else if (tag == 12)
              {
                close nsl_pub(NA_);
                leak nsl_pub(NA_);
              }
              else
              {
                assert false;
              }
            }
            else
            {
              open [_]nsl_pub(pay_);
            }
            assert [_]nsl_pub(NA_);
          }
          else
          {
            assert p1 == receiver && c1 == 1;
            assert some(pay_) == pay1;
            assert [_]message_tag(sig_)(22);
            assert [_]info_for_item(NA_, ?info_NA);
            assert info_NA == int_pair(1, receiver);
            assert NA_creator == sender;
            {
              // Secrecy of NA
              lemma void not_public_na()
                requires  [_]nsl_pub(NA_) &*& [_]info_for_item(NA_, info_NA);
                ensures   false;
              { 
                open [_]nsl_pub(NA_);
                assert [_]info_for_item(NA_, ?info_NA2);
                info_for_item_is_function(NA_, info_NA, info_NA2);
                assert false;
              }
              produce_lemma_function_pointer_chunk(not_public_na) : 
                              not_public(nsl_pub, NA_, info_NA)() { call(); };
            }
          }
        }
    @*/
    item_free(msg);
    item_free(pay);
    item_free(i1);
  }
  
  //@ assert item(NAP, ?NA_, nsl_pub);
  //@ close nonce_request(receiver, int_pair(2, int_pair(sender, receiver)));
  struct item *NBP = create_nonce();
  //@ assert item(NBP, ?NB_, nsl_pub);
  //@ assert [_]info_for_item(NB_, ?info_NB);
  //@ assert info_NB == int_pair(2, int_pair(sender, receiver));
    
  // 2. B -> A. {B,NA,NB}_K(A)
  {
    struct item *i1 = create_pair(NAP, NBP);
    //@ assert item(i1, ?i1_, nsl_pub);
    struct item *i2 = create_pair(B, i1);
    //@ assert item(i2, ?i2_, nsl_pub);
    struct item *msg = asymmetric_authenticated_encryption(sender, KA, 
                                                           KB_PRIVATE, i2);
    //@ assert item(msg, ?msg_, nsl_pub);
    /*@ if (!collision_in_run() )
        {
          assert i1_ == pair_item(NA_, NB_);
          assert i2_ == pair_item(B_, i1_);
          assert msg_ == pair_item(?enc_, ?sig_);
          assert enc_ == asymmetric_encrypted_item(sender, 1, some(?pay_), _);
          assert sig_ == asymmetric_signature_item(recv, 1, some(?msg_id_), _);
          assert msg_id_ == pair_item(A_, hash_item(some(enc_)));
          if (bad(sender))
          {
            get_info_for_item(NA_);
            close nsl_pub(NB_);
            leak nsl_pub(NB_);
            get_info_for_item(B_);
            close nsl_pub(B_);
            leak nsl_pub(B_);
            get_info_for_item(i1_);
            close nsl_pub(i1_);
            leak nsl_pub(i1_);            
            get_info_for_item(i2_);
            close nsl_pub(i2_);
            leak nsl_pub(i2_);
            close message_tag(enc_)(10);
            leak message_tag(enc_)(10);
          }
          else
          {
            assert [_]info_for_item(NA_, ?info_NA);
            assert info_NA == int_pair(1, receiver);
            close message_tag(enc_)(13);
            leak message_tag(enc_)(13);
            {
              // Secrecy of NB
              lemma void not_public_nb()
                requires  [_]nsl_pub(NB_) &*& [_]info_for_item(NB_, info_NB);
                ensures   false;
              { 
                open [_]nsl_pub(NB_);
                assert [_]info_for_item(NB_, ?info_NB2);
                info_for_item_is_function(NB_, info_NB, info_NB2);
                assert false;
              }
              produce_lemma_function_pointer_chunk(not_public_nb) :
                                not_public(nsl_pub, NB_, info_NB)() { call(); };
            }
          }
          get_info_for_item(enc_);
          close nsl_pub(enc_);
          leak nsl_pub(enc_);
          close message_tag(sig_)(23);
          leak message_tag(sig_)(23);
          get_info_for_item(sig_);
          close nsl_pub(sig_);
          leak nsl_pub(sig_);
        }
        else
        {
          get_info_for_item(NA_);
        }
    @*/
    //@ get_info_for_item(msg_);
    //@ close nsl_pub(msg_);
    //@ leak nsl_pub(msg_);
    network_send(net_stat, msg);
    item_free(msg);
    item_free(i1);
    item_free(i2);
  }
  
  //3. A -> B. {NB}_K(B)
  {
    struct item* msg = network_receive(net_stat);
    //@ assert item(msg, ?msg_, nsl_pub);
    struct item* pay =
                    asymmetric_authenticated_decryption(receiver, KA, 
                                                        KB_PRIVATE, msg);
    //@ assert item(pay, ?pay_, nsl_pub);
      if (!item_equals(NBP, pay)) abort();
    /*@ if (!collision_in_run())
        {
          assert msg_ == pair_item(?enc_, ?sig_);
          assert enc_ == asymmetric_encrypted_item(?p1, ?c1, ?pay1_, _);
          assert sig_ == asymmetric_signature_item(sender, 1, some(?msg_id_), _);
          assert msg_id_ == pair_item(B_, ?hash_);
          assert hash_ == hash_item(some(enc_));
          
          open [_]nsl_pub(msg_);
          open [_]nsl_pub(sig_);
          if (!bad(sender))
          {
            assert [_]message_tag(sig_)(24);
          }
        }
    @*/
    item_free(msg);
    item_free(pay);
  }
  
  item_free(A);
  item_free(B);
  item_free(KA);
  *NA = NAP;
  *NB = NBP;
  network_disconnect(net_stat);
  
  return sender;
}
