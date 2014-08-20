#include "nsl.h"
#include "stdlib.h"

#include <stdio.h>

#define RECEIVER_PORT 191919

void sender(int sender, int receiver, struct item *KA_PRIVATE, struct item *KB)
  /*@ requires [?f0]world(nsl_pub) &*&
               generated_values(sender, _) &*&
               !bad(sender) &*& !bad(receiver) &*&
               item(KA_PRIVATE, ?kap) &*& item(KB, ?kb) &*&
               kap == key_item(sender, ?count_kap, private_key, int_pair(0, 0)) &*&
               kb == key_item(receiver, ?count_kb, public_key, int_pair(0, 0));
  @*/
  /*@ ensures  [f0]world(nsl_pub) &*&
               generated_values(sender, _) &*&
               item(KA_PRIVATE, kap) &*& item(KB, kb);
  @*/
{
  struct network_status *net_stat = network_connect("localhost", RECEIVER_PORT);
  
  //1. A -> B. {A,NA}_K(B)
  struct item *NA = 0;
  {
    //@ close nonce_request(sender, int_pair(1, receiver));
    NA = create_nonce();
    
    struct item *i1 = create_data_item(sender); // A
    struct item *i2 = create_pair(i1, NA); // (A, NA)
    struct item *i3 = encrypt(KB, i2); // {(A, NA)}_K(B)
    network_send(net_stat, i3);
    item_free(i1);
    item_free(i2);
    item_free(i3);
  }
   
  // 2. B -> A. {B,NA,NB}_K(A)
  struct item *NB = 0;
  {
    struct item *i4 = network_receive(net_stat);
    struct item *i5 = decrypt(KA_PRIVATE, i4);
    struct item *i6 = pair_get_first(i5);
    int s = item_get_data(i6);
    if (s != receiver) abort();
    struct item *i7 = pair_get_second(i5);
    struct item *i8 = pair_get_first(i7);
    bool eq = item_equals(NA, i8);
    if (!eq) abort();
    NB = pair_get_second(i7);
    item_free(i4);
    item_free(i5);
    item_free(i6);
    item_free(i7);
    item_free(i8);
  }
    
  // 3. A -> B. {NB}_K(B)
  {
    //@ SWITCH_CRYPTO_PRIMITIVES(NB, 1, 1);
    struct item *i9 = encrypt(KB, NB);
    network_send(net_stat, i9);
    item_free(i9);
  }
  
  //Protocol End Goals
  ///////////////////////////////////////////////////////////////////////////
  //1) Secrecy of NA
  //@ assert item(NA, ?na);
  //@ assert !nsl_pub(na);
  //
  //2) Secrecy of NB
  //@ assert item(NB, ?nb);
  //@ assert true == if_no_collision(!nsl_pub(nb));
  //
  //3) Secrecy of KA_PRIVATE
  //@ assert !nsl_pub(kap);
  ///////////////////////////////////////////////////////////////////////////
    
  item_free(NA);
  item_free(NB);
  
  network_disconnect(net_stat);
}

void receiver(int receiver, struct item *KB_PRIVATE)
  /*@ requires [?f0]world(nsl_pub) &*&
               generated_values(receiver, _) &*& !bad(receiver) &*&
               item(KB_PRIVATE, ?kbp) &*&
               kbp == key_item(receiver, ?sskid, private_key, int_pair(0, 0));
  @*/
  /*@ ensures  [f0]world(nsl_pub) &*&
               generated_values(receiver, _) &*& !bad(receiver) &*&
               item(KB_PRIVATE, kbp);
  @*/
{
  struct network_status *net_stat = network_bind_and_accept(RECEIVER_PORT);
  
  // 1. A -> B. {A,NA}_K(B)
  int sender = 0;
  struct item *NA = 0;
  {
    struct item *i0 = network_receive(net_stat);
    struct item *i1 = decrypt(KB_PRIVATE, i0);
    struct item *i2 = pair_get_first(i1);
    sender = item_get_data(i2);
    NA = pair_get_second(i1);
      check_is_nonce(NA);
    item_free(i0);
    item_free(i1);
    item_free(i2);
  }
  
  // 2. B -> A. {B,NA,NB}_K(A)
  struct item *NB = 0;
  {
    struct item *i0 = create_data_item(receiver);
    /*@ close nonce_request(receiver, 
                                int_pair(2, int_pair(sender, receiver))); @*/
    NB = create_nonce();
    //@ assert item(NA, ?na);
    struct item *KA = get_public_key(sender);
    //@ assert item(KA, key_item(sender, _, public_key, _));
      
    struct item *i1 = create_pair(NA, NB);
    struct item *i2 = create_pair(i0, i1);
    struct item *i3 = encrypt(KA, i2);
    network_send(net_stat, i3);
    item_free(i0);
    item_free(i1);
    item_free(i2);
    item_free(i3);
    item_free(KA);
  }
    
  // 3. A -> B. {NB}_K(B)
  {
    struct item *i1 = network_receive(net_stat);
    struct item *i2 = decrypt(KB_PRIVATE, i1);
    bool eq = item_equals(i2, NB);
    if (!eq) abort();
    item_free(i1);
    item_free(i2);
  }
  
  //Protocol End Goals
  ///////////////////////////////////////////////////////////////////////////
  //1) Secrecy of NA
  //@ assert item(NA, ?na) &*& na == nonce_item(?na_p, ?na_c, ?na_inc, ?na_i);
  //@ assert bad(sender) || if_no_collision(!nsl_pub(na));
  //
  //2) Secrecy of NB
  //@ assert item(NB, ?nb);
  //@ assert bad(sender) || !nsl_pub(nb);
  //
  //3) Secrecy of KB_PRIVATE
  //@ assert !nsl_pub(kbp);
  ///////////////////////////////////////////////////////////////////////////

  item_free(NA);
  item_free(NB);
  
  network_disconnect(net_stat);
}
