#include "nsl.h"
#include "stdlib.h"

#include <stdio.h>

#define RECEIVER_PORT 121212

void sender(int sender, int receiver, struct item *KA_PRIVATE, struct item *KB)
  /*@ requires generated_nonces(sender, _) &*& 
               [?f]world(nsl_pub) &*& !bad(sender) &*& !bad(receiver) &*&
               key_item(KA_PRIVATE, sender, ?cskid, private_key, int_pair(0, 0)) &*&
               key_item(KB, receiver, ?spkid, public_key, int_pair(0, 0));
  @*/
  /*@ ensures  generated_nonces(sender, _) &*&
               [f]world(nsl_pub) &*&
               key_item(KA_PRIVATE, sender, cskid, private_key, int_pair(0, 0)) &*&
               key_item(KB, receiver, spkid, public_key, int_pair(0, 0));
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
  //@ assert item(NA, ?cn);
  //@ assert !nsl_pub(cn);
  //
  //2) Secrecy of NB
  //@ assert item(NB, ?sn);
  //@ assert !nsl_pub(sn);
  //
  //3) Secrecy of KA_PRIVATE
  //@ assert !nsl_pub(key_item(sender, cskid, private_key, int_pair(0, 0)));
  ///////////////////////////////////////////////////////////////////////////
    
  item_free(NA);
  item_free(NB);
  
  network_disconnect(net_stat);
}

void receiver(int receiver, struct item *KB_PRIVATE)
  /*@ requires generated_nonces(receiver, _) &*&
               [?f]world(nsl_pub) &*& !bad(receiver) &*&
               key_item(KB_PRIVATE, receiver, ?sskid, private_key, int_pair(0, 0)); 
  @*/
  /*@ ensures generated_nonces(receiver, _) &*&
               [f]world(nsl_pub) &*& !bad(receiver) &*&
               key_item(KB_PRIVATE, receiver, sskid, private_key, int_pair(0, 0)); 
  @*/
{
  struct network_status *net_stat = network_bind(RECEIVER_PORT);
  
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
    //@ assert item(NA, ?cn);
    //@ close public_key_request(int_pair(0, 0));
    struct item *KA = get_public_key(sender);
      /*@ close nonce_request(receiver, 
                                int_pair(2, int_pair(sender, receiver))); @*/
      
    //@ assert key_item(KA, sender, _, public_key, int_pair(0, 0));
    NB = create_nonce();
    struct item *i0 = create_data_item(receiver);
    //@ assert item(i0, data_item(receiver));
    //@ assert item(NA, nonce_item(?sss, _, ?iii));
    /*@ assert item(NB, nonce_item(
                  receiver, _, int_pair(2 , int_pair(sender, receiver)))); @*/
    /*@ assert
          bad(sss) || 
        (int_left(iii) == 1 && bad(int_right(iii))) ||
        (int_left(iii) == 2 && bad(int_left(int_right(iii)))) ||
        (sss == sender && iii == int_pair(1, receiver));
    @*/
    struct item *i1 = create_pair(NA, NB);
    struct item *i2 = create_pair(i0, i1);
    struct item *i3 = encrypt(KA, i2);
    network_send(net_stat, i3);
    item_free(i0);
    item_free(i1);
    item_free(i2);
    item_free(i3);
    key_free(KA);
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
  //@ assert item(NA, nonce_item(?na_p, ?na_c, ?na_i));
  /*@ assert bad(na_p) || 
              (int_left(na_i) == 1 && bad(int_right(na_i))) ||
              (int_left(na_i) == 2 && bad(int_left(int_right(na_i)))) ||
              !nsl_pub(nonce_item(na_p, na_c, na_i));
  @*/
  //2) Secrecy of NB
  //@ assert item(NB, ?ns);
  //@ assert bad(sender) || !nsl_pub(ns);
  //
  //3) Secrecy of KB_PRIVATE
  //@ assert !nsl_pub(key_item(receiver, sskid, private_key, int_pair(0, 0)));
  ///////////////////////////////////////////////////////////////////////////

  item_free(NA);
  item_free(NB);
  
  network_disconnect(net_stat);
}
