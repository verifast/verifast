#include "yahalom.h"
#include "stdlib.h"

#define SERVER_PORT 343434
#define RECVER_PORT 232323
#define SENDER_PORT 121212


struct item *sender(char sender, char receiver, struct item *KAS)
  /*@ requires [?f0]world(yahalom_pub) &*&
               !bad(server_id()) &*& !bad(sender) &*& !bad(receiver) &*&
               generated_values(sender, ?count) &*& 
               item(KAS, ?kas, yahalom_pub) &*& 
                 [_]info_for_item(kas, ?i_kas) &*&
                 kas == symmetric_key_item(sender, _) &*& 
                 i_kas == int_pair(2, 0); @*/
  /*@ ensures  [f0]world(yahalom_pub) &*&
               generated_values(sender, ?count2) &*& count2 >= count &*&
               item(KAS, kas, yahalom_pub) &*& 
               item(result, ?kab, yahalom_pub) &*& 
                 [_]info_for_item(kab, ?i_kab) &*&
                 kab == symmetric_key_item(?p_kab, ?c_kab) &*&
               collision_in_run() ?
                 true
               :
                 p_kab == server_id() &*&
                 i_kab == int_pair(3, int_pair(sender, receiver)) &*&
                 // Secrecy of KAB
                 is_not_public(_, yahalom_pub, kab, i_kab) &*&
                 // Secrecy of KAS
                 is_not_public(_, yahalom_pub, kas, i_kas); @*/
{
  struct network_status *net_stat_out = 
                                      network_connect("localhost", RECVER_PORT);
  struct network_status *net_stat_in  = network_bind_and_accept(SENDER_PORT);
  
  struct item *i1;
  struct item *i2;
  struct item *i3;
  struct item *i4;
  struct item *i5;
  struct item *i6;
  struct item *i7;
  struct item *i8;
  
  //@ item A_data = data_item(cons(sender, nil));
  //@ item B_data = data_item(cons(receiver, nil));
  //@ assert character(&sender, ?send);
  struct item *A = create_data_item(&sender, 1); 
  //@ open chars(&sender, _, cons(send, nil));
  //@ assert item(A, A_data, yahalom_pub);
  //@ get_info_for_item(A_data);
  //@ close yahalom_pub(A_data);
  //@ leak yahalom_pub(A_data);
  //@ assert character(&receiver, ?recv);
  struct item *B = create_data_item(&receiver, 1); 
  //@ open chars(&receiver, _, cons(recv, nil));
  //@ assert item(B, B_data, yahalom_pub);
  //@ close nonce_request(sender, int_pair(0, 0));
  struct item *NA = create_nonce();
  //@ item NA_nonce = nonce_item(sender, count + 1, 0);
  //@ assert item(NA, NA_nonce, yahalom_pub);
  //@ close yahalom_pub(NA_nonce);
  //@ leak yahalom_pub(NA_nonce);
  
  // 1. A -> B. A, NA
  i1 = create_pair(A, NA);
  //@ item msg1 = pair_item(A_data, NA_nonce);
  //@ assert item(i1, msg1, yahalom_pub);
  //@ get_info_for_item(msg1);
  //@ close yahalom_pub(msg1);
  //@ leak yahalom_pub(msg1);
  network_send(net_stat_out, i1);
  item_free(i1);
  
  // 3. S -> A. {B, K(AB), NA, NB}_K(AS), {A, K(AB)}_K(BS)
  i1 = network_receive(net_stat_in);
  //@ assert item(i1, ?msg2, yahalom_pub);
  i2 = pair_get_first(i1);
  //@ assert item(i2, ?msg2_1, yahalom_pub);
  struct item *B_S = pair_get_second(i1);
  //@ assert item(B_S, ?msg2_2, yahalom_pub);
    check_is_symmetric_encrypted(i2);
  i3 = symmetric_decryption(KAS, i2);
  //@ assert item(i3, ?msg2_1_pay, yahalom_pub);
  i4 = pair_get_first(i3); // B
    // check B
    if (!item_equals(B, i4)){abort();}
  i5 = pair_get_second(i3);
  //@ assert item(i4, ?i4_2, yahalom_pub);
  //@ assert item(i5, ?i5_2, yahalom_pub);
  struct item *KAB = pair_get_first(i5); // K(AB)
    // check KAB
    check_is_symmetric_key(KAB);
  //@ assert item(KAB, ?KAB_, yahalom_pub);
  i6 = pair_get_second(i5);
  //@ assert item(i6, ?i6_2, yahalom_pub);
  i7 = pair_get_first(i6); // NA
    // check NA
    if (!item_equals(NA, i7)){abort();}
  struct item *NB = pair_get_second(i6); // NB
    // check NB
    check_is_nonce(NB);  
  //@ assert item(i7, ?i7_2, yahalom_pub);
  //@ assert item(NB, ?NB_, yahalom_pub);
  item_free(i1);
  item_free(i2);
  item_free(i3);
  item_free(i4);
  item_free(i5);
  item_free(i6);
  item_free(i7);
  
  // 4. A -> B. {A, K(AB)}_K(BS), {NB}_K(AB)
  i1 = symmetric_encryption(KAB, NB);
  //@ assert item(i1, ?msg3_2, yahalom_pub);
  i2 = create_pair(B_S, i1);
  //@ assert item(i2, ?msg3, yahalom_pub);
  
  /*@ if (!collision_in_run())
      {
        assert msg2_1 == symmetric_encrypted_item(
                            send, _, some(msg2_1_pay), ?ent1);
        assert msg2_1_pay == pair_item(B_data, 
                                     pair_item(KAB_, pair_item(NA_nonce, NB_)));
        open [_]yahalom_pub(msg2);
        open [_]yahalom_pub(msg2_1);
        info_for_symmetric_encrypted_item(kas, msg2_1);
        assert [_]info_for_item(msg2_1, ?info0);
        assert [_]info_for_item(KAB_, ?info1);
        assert [_]info_for_item(NB_, ?info2);
        
        assert KAB_ == symmetric_key_item(?p0, ?c0);
        assert msg3 == pair_item(?msg3_1, msg3_2);
        assert msg3_1 == msg2_2;
        assert msg3_2 == symmetric_encrypted_item(p0, c0, some(NB_), ?ent2);
        assert [_]yahalom_pub(msg3_1);
        
        get_info_for_item(msg3_2);
        info_for_symmetric_encrypted_item(KAB_, msg3_2);
        close yahalom_pub(msg3_2);
        leak yahalom_pub(msg3_2);
        
        {
          // Secrecy of KAS
          lemma void not_public_kas()
            requires  [_]yahalom_pub(kas) &*& [_]info_for_item(kas, i_kas);
            ensures   false;
          { 
            open [_]yahalom_pub(kas);
            assert [_]info_for_item(kas, ?i_kas2);
            info_for_item_is_function(kas, i_kas, i_kas2);
            assert false;
          }
          // Secrecy of KAB
          lemma void not_public_kab()
            requires  [_]yahalom_pub(KAB_) &*& [_]info_for_item(KAB_, info1);
            ensures   false;
          { 
            open [_]yahalom_pub(KAB_);
            assert [_]info_for_item(KAB_, ?info1_2);
            info_for_item_is_function(KAB_, info1, info1_2);
            assert false;
          }
          // Secrecy of NB
          lemma void not_public_nb()
            requires  [_]yahalom_pub(NB_) &*& [_]info_for_item(NB_, info2);
            ensures   false;
          { 
            open [_]yahalom_pub(NB_);
            assert [_]info_for_item(NB_, ?info2_2);
            info_for_item_is_function(NB_, info2, info2_2);
            assert false;
          }
          produce_lemma_function_pointer_chunk(not_public_kas) : 
                              not_public(yahalom_pub, kas, i_kas)() { call(); };
          produce_lemma_function_pointer_chunk(not_public_kab) : 
                             not_public(yahalom_pub, KAB_, info1)() { call(); };
        }
      }
      else
      {
        get_info_for_item(KAB_);
      }
  @*/
  //@ get_info_for_item(msg3);
  //@ close yahalom_pub(msg3);
  //@ leak yahalom_pub(msg3);
 
  network_send(net_stat_out, i2);
  item_free(i1);
  item_free(i2);
  item_free(A);
  item_free(B);
  item_free(NA);
  item_free(NB);
  item_free(B_S);
  
  network_disconnect(net_stat_in);
  network_disconnect(net_stat_out);
  
  return KAB;
}

void receiver(char receiver, struct item * KBS)
  /*@ requires [?f0]world(yahalom_pub) &*&
               !bad(server_id()) &*& !bad(receiver) &*&
               generated_values(receiver, ?count) &*& 
               item(KBS, ?kbs, yahalom_pub) &*& 
                 [_]info_for_item(kbs, ?i_kbs) &*&
                 kbs == symmetric_key_item(receiver, _) &*& 
                 i_kbs == int_pair(2, 0); @*/
  /*@ ensures  [f0]world(yahalom_pub) &*&
               generated_values(receiver, ?count2) &*& count2 >= count &*&
               item(KBS, kbs, yahalom_pub); @*/
{
  struct network_status *net_stat_in  = network_bind_and_accept(RECVER_PORT);
  struct network_status *net_stat_out = network_connect("localhost", SERVER_PORT);
  
  char *buffer;
  struct item *i1;
  
  // 1. A -> B. A, NA
  i1 = network_receive(net_stat_in);
  //@ assert item(i1, ?i1_, yahalom_pub);
  
  struct item *A = pair_get_first(i1);
  check_is_data(A);
  //@ assert item(A, ?A_, yahalom_pub);
  if (item_get_data(A, &buffer) != 1) abort();
  //@ assert pointer(&buffer, ?p);
  //@ pointer_limits(&buffer);
  //@ chars_limits(p);
  //@ open chars(p, 1, _);
  //@ open chars(p + 1, 0, _);
  char sender = *buffer;
  //@ assert collision_in_run() ? true : A_ == data_item(cons(sender, nil));
  free(buffer);
  
  struct item *NA = pair_get_second(i1); // NA
  //@ assert item(NA, ?NA_, yahalom_pub);
  check_is_nonce(NA);
  item_free(i1);
  //@ open [_]yahalom_pub(i1_);
  /*@ if (collision_in_run) 
      {
        close yahalom_pub(NA_);
        leak yahalom_pub(NA_);
      }
  @*/
  
  struct item* KAB = 
            core_receiver(net_stat_in, net_stat_out, sender, NA, receiver, KBS);
  //@ if (!collision_in_run()) leak is_not_public(_, yahalom_pub, kbs, i_kbs);
  //@ assert item(KAB, ?kab, yahalom_pub);
  /*@ if (!collision_in_run() && !bad(sender)) 
        leak is_not_public(_, yahalom_pub, kab, _); @*/
  
  item_free(A);
  item_free(KAB);
  
  network_disconnect(net_stat_in);
  network_disconnect(net_stat_out);
}
    
struct item *core_receiver(struct network_status *net_stat_in,
                           struct network_status *net_stat_out, char sender,
                           struct item* NA, char receiver, struct item * KBS)
  /*@ requires [?f0]world(yahalom_pub) &*&
               network_status(net_stat_in) &*& network_status(net_stat_out) &*&
               !bad(server_id()) &*& !bad(receiver) &*&
               generated_values(receiver, ?count) &*& 
               item(KBS, ?kbs, yahalom_pub) &*& 
                 [_]info_for_item(kbs, ?i_kbs) &*&
                 kbs == symmetric_key_item(receiver, _) &*& 
                 i_kbs == int_pair(2, 0) &*&
               item(NA, ?na, yahalom_pub) &*& [_]yahalom_pub(na); @*/
  /*@ ensures  [f0]world(yahalom_pub) &*&
               network_status(net_stat_in) &*& network_status(net_stat_out) &*&
               generated_values(receiver, ?count2) &*& count2 >= count &*&
               item(KBS, kbs, yahalom_pub) &*&
               item(result, ?kab, yahalom_pub) &*& 
                 [_]info_for_item(kab, ?i_kab) &*&
                 kab == symmetric_key_item(?p_kab, ?c_kab) &*&
               collision_in_run() ? true : 
               (
                 is_not_public(_, yahalom_pub, kbs, i_kbs) &*&
                 p_kab == server_id() &*&
                 i_kab == int_pair(3, int_pair(sender, receiver)) &*&
                 bad(sender) ?
                   true
                 :
                   is_not_public(_, yahalom_pub, kab, i_kab)
               ); @*/
{
  struct item *i1;
  struct item *i2;
  struct item *i3;
  struct item *i4;
  struct item *i5;
  struct item *i6;
  
  //@ item A_ = data_item(cons(sender, nil));
  //@ item B_ = data_item(cons(receiver, nil));
  //@ assert character(&sender, ?send);
  struct item *A = create_data_item(&sender, 1); 
  //@ open chars(&sender, _, cons(send, nil));
  //@ assert item(A, A_, yahalom_pub);
  //@ assert character(&receiver, ?recv);
  struct item *B = create_data_item(&receiver, 1); 
  //@ open chars(&receiver, _, cons(recv, nil));
  //@ assert item(B, B_, yahalom_pub);
  //@ get_info_for_item(B_);
  //@ close yahalom_pub(B_);
  //@ leak yahalom_pub(B_);
  
  // 2. B -> S. B, {A, NA, NB}_K(BS)
  //@ close nonce_request(receiver, int_pair(1, sender));
  //@ item NB_ = nonce_item(receiver, count + 1, 0);
  struct item *NB = create_nonce();
  //@ assert item(NB, NB_, yahalom_pub);
  //@ assert [_]info_for_item(NB_, ?i_NB_);
  //@ assert i_NB_ == int_pair(1, sender);
  
  i1 = create_pair(NA, NB);
  //@ assert item(i1, ?i1_1, yahalom_pub);
  i2 = create_pair(A, i1);
  //@ assert item(i2, ?i2_1, yahalom_pub);
  i3 = symmetric_encryption(KBS, i2);
  //@ assert item(i3, ?i3_1, yahalom_pub);
  i4 = create_pair(B, i3);
  //@ assert item(i4, ?i4_1, yahalom_pub);
  
  /*@ if (!collision_in_run)
      {
        assert i1_1 == pair_item(na, NB_);
        assert i2_1 == pair_item(A_, i1_1);
        assert i3_1 == symmetric_encrypted_item(recv, _, some(i2_1), ?ent);
        assert i4_1 == pair_item(B_, i3_1);
        get_info_for_item(i3_1);
        assert [_]info_for_item(i3_1, ?i_i3_1);
        info_for_symmetric_encrypted_item(kbs, i3_1);
        close yahalom_pub(i3_1);
        leak yahalom_pub(i3_1);
      }
  @*/
  //@ get_info_for_item(i4_1);
  //@ close yahalom_pub(i4_1);
  //@ leak yahalom_pub(i4_1);
  network_send(net_stat_out, i4);
  
  item_free(i1);
  item_free(i2);
  item_free(i3);
  item_free(i4);
  
  // 4. A -> B. {A, K(AB)}_K(BS), {NB}_K(AB)
  i1 = network_receive(net_stat_in);
  //@ assert item(i1, ?i1_2, yahalom_pub);
  i2 = pair_get_first(i1);
    check_is_symmetric_encrypted(i2);
  //@ assert item(i2, ?i2_2, yahalom_pub);
  i3 = pair_get_second(i1);
    check_is_symmetric_encrypted(i3);
  //@ assert item(i3, ?i3_2, yahalom_pub);
  i4 = symmetric_decryption(KBS, i2);
  //@ assert item(i4, ?i4_2, yahalom_pub);
  i5 = pair_get_first(i4);
  //@ assert item(i5, ?i5_2, yahalom_pub);
    if (!item_equals(A, i5)){abort();}  
  struct item *KAB = pair_get_second(i4);
    check_is_symmetric_key(KAB);
  i6 = symmetric_decryption(KAB, i3);
  //@ assert item(KAB, ?KAB_, yahalom_pub);
    if (!item_equals(NB, i6)){abort();}
  //@ assert item(i6, ?i6_, yahalom_pub);
  item_free(i1);
  item_free(i2);
  item_free(i3);
  item_free(i4);
  item_free(i5);
  item_free(i6);
  
  /*@ if (!collision_in_run)
      {
        assert i1_2 == pair_item(i2_2, i3_2);
        assert i2_2 == symmetric_encrypted_item(recv, _, some(i4_2), _);
        assert i3_2 == symmetric_encrypted_item(?p0, ?c0, some(NB_), _);
        assert i4_2 == pair_item(i5_2, KAB_);
        assert i5_2 == data_item(cons(send, nil));
        assert KAB_ == symmetric_key_item(p0, c0);
        assert i6_ == NB_;
        
        open [_]yahalom_pub(i1_2);
        open [_]yahalom_pub(i2_2);
        assert [_]info_for_item(i2_2, ?i2_2_);
        info_for_symmetric_encrypted_item(kbs, i2_2);
        open [_]yahalom_pub(i3_2);
        assert [_]info_for_item(i3_2, ?i3_2_);
        assert [_]info_for_item(KAB_, ?i_KAB_);
        info_for_symmetric_encrypted_item(KAB_, i3_2);
        
        assert [_]info_for_item(KAB_, i3_2_);
        assert i3_2_ == int_pair(3, int_pair(send, recv));
        assert [_]info_for_item(i6_, ?i_i6_);
        info_for_item_is_function(NB_, i_NB_, i_i6_);
        
        {
          // Secrecy of KBS
          lemma void not_public_kbs()
            requires  [_]yahalom_pub(kbs) &*& [_]info_for_item(kbs, i_kbs);
            ensures   false;
          { 
            open [_]yahalom_pub(kbs);
            assert [_]info_for_item(kbs, ?i_kbs2);
            info_for_item_is_function(kbs, i_kbs, i_kbs2);
            assert false;
          }
          if (!bad(send))
          {
            // Secrecy of KAB
            lemma void not_public_kab()
              requires  [_]yahalom_pub(KAB_) &*& [_]info_for_item(KAB_, i_KAB_);
              ensures   false;
            { 
              open [_]yahalom_pub(KAB_);
              assert [_]info_for_item(KAB_, ?i_KAB_2);
              info_for_item_is_function(KAB_, i_KAB_, i_KAB_2);
              assert false;
            }
            // Secrecy of NB
            lemma void not_public_nb()
              requires  [_]yahalom_pub(NB_) &*& [_]info_for_item(NB_, i_NB_);
              ensures   false;
            { 
              open [_]yahalom_pub(NB_);
              assert [_]info_for_item(NB_, ?i_NB_2);
              info_for_item_is_function(NB_, i_NB_, i_NB_2);
              assert false;
            }
            produce_lemma_function_pointer_chunk(not_public_kab) : 
                            not_public(yahalom_pub, KAB_, i_KAB_)() { call(); };
          }
          produce_lemma_function_pointer_chunk(not_public_kbs) : 
                              not_public(yahalom_pub, kbs, i_kbs)() { call(); };
        }
      }
      else
      {
        get_info_for_item(KAB_);
      }
  @*/
    
  item_free(A);
  item_free(B);
  item_free(NA);
  item_free(NB);
  
  return KAB;
}

void server(char sender, char receiver, struct item *KAS, 
            struct item *KBS, struct item *KAB)
  /*@ requires [?f]world(yahalom_pub) &*&
               !bad(server_id()) &*& !bad(sender) &*& !bad(receiver) &*&
               generated_values(server_id(), ?count) &*&
               item(KAS, ?kas, yahalom_pub) &*& 
                 [_]info_for_item(kas, ?i_kas) &*&
                 kas == symmetric_key_item(sender, _) &*& 
                 i_kas == int_pair(2,0) &*&
               item(KBS, ?kbs, yahalom_pub) &*& 
                 [_]info_for_item(kbs, ?i_kbs) &*&
                 kbs == symmetric_key_item(receiver, _) &*& 
                 i_kbs == int_pair(2,0) &*&
               item(KAB, ?kab, yahalom_pub) &*& 
                 [_]info_for_item(kab, ?i_kab) &*&
                 kab == symmetric_key_item(server_id(), _) &*& 
                 i_kab == int_pair(3, int_pair(sender, receiver)); @*/
  /*@ ensures [f]world(yahalom_pub) &*&
              generated_values(server_id(), ?count2) &*& count2 >= count &*&
              item(KAS, kas, yahalom_pub) &*& 
              item(KBS, kbs, yahalom_pub) &*& 
              item(KAB, kab, yahalom_pub) &*&
              collision_in_run() ? true :
              (
                is_not_public(_, yahalom_pub, kas, i_kas) &*&
                is_not_public(_, yahalom_pub, kbs, i_kbs) &*&
                is_not_public(_, yahalom_pub, kab, i_kab)
              ); @*/
{
  struct network_status *net_stat_in  = network_bind_and_accept(SERVER_PORT);
  struct network_status *net_stat_out = network_connect("localhost", SENDER_PORT);
  
  struct item *i1;
  struct item *i2;
  struct item *i3;
  struct item *i4;
  struct item *i5;
  struct item *i6;
  struct item *i7;
  
  //@ item A_ = data_item(cons(sender, nil));
  //@ item B_ = data_item(cons(receiver, nil));
  //@ assert character(&sender, ?send);
  struct item *A = create_data_item(&sender, 1); 
  //@ open chars(&sender, _, cons(send, nil));
  //@ assert item(A, A_, yahalom_pub);
  //@ assert character(&receiver, ?recv);
  struct item *B = create_data_item(&receiver, 1); 
  //@ open chars(&receiver, _, cons(recv, nil));
  //@ assert item(B, B_, yahalom_pub);
  
  // 2. B -> S. B, {A, NA, NB}_K(BS)
  i1 = network_receive(net_stat_in);
  //@ assert item(i1, ?i1_1, yahalom_pub);
  i2 = pair_get_first(i1);
    if (!item_equals(B, i2)){abort();}
  //@ assert item(i2, ?i2_1, yahalom_pub);
  i3 = pair_get_second(i1);
    check_is_symmetric_encrypted(i3);
  //@ assert item(i3, ?i3_1, yahalom_pub);
  i4 = symmetric_decryption(KBS, i3);
  //@ assert item(i4, ?i4_1, yahalom_pub);
  i5 = pair_get_first(i4);
    if (!item_equals(A, i5)){abort();}
  //@ assert item(i5, ?i5_1, yahalom_pub);
  i6 = pair_get_second(i4);
  //@ assert item(i6, ?i6_1, yahalom_pub);
  struct item* NA = pair_get_first(i6);
    check_is_nonce(NA);
  //@ assert item(NA, ?NA_, yahalom_pub);
  struct item* NB = pair_get_second(i6);
    check_is_nonce(NB);
  //@ assert item(NB, ?NB_, yahalom_pub);
  item_free(i1);
  item_free(i2);
  item_free(i3);
  item_free(i4);
  item_free(i5);
  item_free(i6);
  
  // 3. S -> A. {B, K(AB), NA, NB}_K(AS), {A, K(AB)}_K(BS)
  i1 = create_pair(A, KAB);
  //@ assert item(i1, ?i1_2, yahalom_pub);
  i2 = symmetric_encryption(KBS, i1);
  //@ assert item(i2, ?i2_2, yahalom_pub);
  i3 = create_pair(NA, NB);
  //@ assert item(i3, ?i3_2, yahalom_pub);
  i4 = create_pair(KAB, i3);
  //@ assert item(i4, ?i4_2, yahalom_pub);
  i5 = create_pair(B, i4);
  //@ assert item(i5, ?i5_2, yahalom_pub);
  i6 = symmetric_encryption(KAS, i5);
  //@ assert item(i6, ?i6_2, yahalom_pub);
  i7 = create_pair(i6, i2);
  //@ assert item(i7, ?i7_2, yahalom_pub);
  
  /*@ if (!collision_in_run)
      {
        assert i1_1 == pair_item(i2_1, i3_1);
        assert i2_1 == B_;
        assert i3_1 == symmetric_encrypted_item(recv, _, some(i4_1), _);
        assert i4_1 == pair_item(i5_1, i6_1);
        assert i5_1 == A_;
        assert i6_1 == pair_item(NA_, NB_);
        
        open [_]yahalom_pub(i1_1);
        open [_]yahalom_pub(i3_1);
        assert [_]info_for_item(i3_1, ?i_i3_1);
        info_for_symmetric_encrypted_item(kbs, i3_1);
        assert [_]info_for_item(NB_, ?i_NB_);
        assert i_NB_ == int_pair(1, send);
        
        assert i1_2 == pair_item(A_, kab);
        assert i2_2 == symmetric_encrypted_item(recv, _, some(i1_2), _);
        assert i3_2 == pair_item(NA_, NB_);
        assert i4_2 == pair_item(kab, i3_2);
        assert i5_2 == pair_item(B_, i4_2);
        assert i6_2 == symmetric_encrypted_item(send, _, some(i5_2), _);
        assert i7_2 == pair_item(i6_2, i2_2);
        
        get_info_for_item(i2_2);
        info_for_symmetric_encrypted_item(kbs, i2_2);
        close yahalom_pub(i2_2);
        leak yahalom_pub(i2_2);
        get_info_for_item(i6_2);
        info_for_symmetric_encrypted_item(kas, i6_2);
        close yahalom_pub(i6_2);
        leak yahalom_pub(i6_2);
        get_info_for_item(i7_2);
        close yahalom_pub(i7_2);
        leak yahalom_pub(i7_2);
        
        {
          // Secrecy of KAS
          lemma void not_public_kas()
            requires  [_]yahalom_pub(kas) &*& [_]info_for_item(kas, i_kas);
            ensures   false;
          { 
            open [_]yahalom_pub(kas);
            assert [_]info_for_item(kas, ?i_kas2);
            info_for_item_is_function(kas, i_kas, i_kas2);
            assert false;
          }
          // Secrecy of KBS
          lemma void not_public_kbs()
            requires  [_]yahalom_pub(kbs) &*& [_]info_for_item(kbs, i_kbs);
            ensures   false;
          { 
            open [_]yahalom_pub(kbs);
            assert [_]info_for_item(kbs, ?i_kbs2);
            info_for_item_is_function(kbs, i_kbs, i_kbs2);
            assert false;
          }
          // Secrecy of AB
          lemma void not_public_kab()
            requires  [_]yahalom_pub(kab) &*& [_]info_for_item(kab, i_kab);
            ensures   false;
          { 
            open [_]yahalom_pub(kab);
            assert [_]info_for_item(kab, ?i_kab_2);
            info_for_item_is_function(kab, i_kab, i_kab_2);
            assert false;
          }
          produce_lemma_function_pointer_chunk(not_public_kas) : 
                              not_public(yahalom_pub, kas, i_kas)() { call(); };
          produce_lemma_function_pointer_chunk(not_public_kbs) : 
                              not_public(yahalom_pub, kbs, i_kbs)() { call(); };
          produce_lemma_function_pointer_chunk(not_public_kab) : 
                              not_public(yahalom_pub, kab, i_kab)() { call(); };
        }
      }
      else
      {
        close yahalom_pub(i7_2);
        leak yahalom_pub(i7_2);
      }
  @*/
  
  network_send(net_stat_out, i7);
  item_free(i1);
  item_free(i2);
  item_free(i3);
  item_free(i4);
  item_free(i5);
  item_free(i6);
  item_free(i7);
  
  item_free(A);
  item_free(B);
  item_free(NA);
  item_free(NB);
  
  network_disconnect(net_stat_in);
  network_disconnect(net_stat_out);
}
