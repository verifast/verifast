#include "nss.h"
#include "stdlib.h"

#define SERVER_PORT 121212
#define RECVER_PORT 232323

///////////////////////////////////////////////////////////////////////////////
// Protocol implementation ////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *sender(int sender, int receiver, struct item * KAS)
  /*@ requires 
        [?f0]world(nss_pub) &*&
        !bad(server_id()) &*& !bad(sender) &*& !bad(receiver) &*&
        generated_values(sender, ?count) &*& 
        item(KAS, ?kas) &*& 
        kas == key_item(sender, 1, symmetric_key, int_pair(0, 0));
  @*/
  /*@ ensures 
        [f0]world(nss_pub) &*&
        generated_values(sender, ?count2) &*& count2 >= count &*&
        item(KAS, kas) &*& nss_pub(kas) == false &*&
        item(result, ?kab) &*& kab == key_item(?p0, ?c0, ?k0, ?i0) &*&
        collision_in_run() ? 
          true 
        : 
          (
            p0 == server_id() &&
            k0 == symmetric_key &&
            i0 == int_pair(2, int_pair(sender, receiver))&&
            nss_pub(kab) == false
          );
  @*/
{ 
  struct network_status *net_stat = network_connect("localhost", RECVER_PORT);
  struct network_status *net_stat_serv = 
                                    network_connect("localhost", SERVER_PORT);
  // 1. A -> B. A
  struct item *A = 0;
  {
    A = create_data_item(sender);
    network_send(net_stat, A);  
  }
  
  // 2. B -> A. {A, NB1}_K(BS)
  struct item *B_S1 = 0;
  {
    B_S1 = network_receive(net_stat);  
  }
  
  // 3. A -> S. A, B, NA, {A, NB1}_K(BS)
  struct item *B;
  struct item *NA;
  {
    B = create_data_item(receiver);
    //@ close nonce_request(sender, int_pair(4, receiver));
    NA = create_nonce();
    struct item *i1 = create_pair(NA, B_S1); //        (NA, {A, NB1}_K(BS))
    struct item *i2 = create_pair(B, i1);    //    (B, (NA, {A, NB1}_K(BS)))
    struct item *i3 = create_pair(A, i2);    // (A, B, (NA, {A, NB1}_K(BS))))
    network_send(net_stat_serv, i3);
    item_free(i1);
    item_free(i2);
    item_free(i3);
  }
  
  // 4. S -> A. {NA, K(AB), B, {K(AB), A, NB1}_K(BS)}_K(AS)
  struct item *KAB = 0;
  struct item *B_S2 = 0;
  {
    struct item *i1 = network_receive(net_stat_serv);
    struct item *i2 = decrypt(KAS, i1);    // (NA, (K(AB), (B, {K(AB), A, NB1}_K(BS))))
    struct item *i3 = pair_get_first(i2);  //  NA
    struct item *i4 = pair_get_second(i2); //      (K(AB), (B, {K(AB), A, NB1}_K(BS)))
    KAB = pair_get_first(i4);              //       K(AB)
    struct item *i5 = pair_get_second(i4); //              (B, {K(AB), A, NB1}_K(BS))
    struct item *i6 = pair_get_first(i5);  //               B
    B_S2 = pair_get_second(i5);            //                  {K(AB), A, NB1}_K(BS)
      // check NA
      if (!item_equals(i3, NA)){abort();}
      // check B
      if (!item_equals(i6, B)){abort();}
      // check KAB
      check_is_key(KAB);
    item_free(i1);
    item_free(i2);
    item_free(i3);
    item_free(i4);
    item_free(i5);
    item_free(i6);
  }
  
  //@ assert item(KAB, key_item(?p0, ?c0, ?k0, ?i0));
  //@ collision_in_run() ? true : p0 == 0;
  //@ collision_in_run() ? true : k0 == symmetric_key;
  //@ collision_in_run() ? true : i0 == int_pair(2, int_pair(sender, receiver));
  
  // 5. A -> B. {K(AB), A, NB1}_K(BS)
  {
    network_send(net_stat, B_S2);
  }
  
  // 6. B -> A. {NB2, 0}_K(AB)
  struct item *NB2 = 0;
  {
    struct item *i1 = network_receive(net_stat);
    struct item *i2 = decrypt(KAB, i1);    // (NB2, 0)
    NB2 = pair_get_first(i2);              //  NB2
    struct item *i3 = pair_get_second(i2); //       0
      int tag = item_get_data(i3);
      // check tag
      if (tag != 0){abort();}
      // check NB2
      check_is_nonce(NB2);
    item_free(i1);
    item_free(i2);
    item_free(i3);
  }
  
  //@ assert item(NB2, nonce_item(?pp1, ?cc1, ?inc1, ?ii1));
  //@ collision_in_run() ? true : pp1  == receiver;
  //@ collision_in_run() ? true : inc1 == 0;
  //@ collision_in_run() ? true : ii1  == int_pair(5, sender);
  
  // 7. A -> B. {NB2 + 1, 1}_K(AB)
  struct item *NB22 = 0;
  {
    NB22 = item_clone(NB2);
    increment_nonce(NB22);                   //   NB2 + 1
    struct item *i1 = create_data_item(1);   //            1
    struct item *i2 = create_pair(NB22, i1); //  (NB2 + 1, 1)
    struct item *i3 = encrypt(KAB, i2);      // {(NB2 + 1, 1)}_K(AB)
    network_send(net_stat, i3);
    item_free(i1);
    item_free(i2);
    item_free(i3);
  }
  
    //Protocol End Goals
    ///////////////////////////////////////////////////////////////////////////
    //1) Secrecy of NB2
    //@  assert item(NB2, ?nb2);
    //@  assert collision_in_run() ? true : (nss_pub(nb2) == false);
    //
    //2) Secrecy of NB2 + 1
    //@  assert item(NB22, ?nb22);
    //@  assert collision_in_run() ? true : (nss_pub(nb22) == false);
    //
    //3) Secrecy of KAS
    //@ assert item(KAS, kas);
    //@ assert nss_pub(kas) == false;
    //
    //4) Secrecy of KAB
    //@ assert item(KAB, ?kab);
    //@ assert collision_in_run() ? true : (nss_pub(kab) == false);
    ///////////////////////////////////////////////////////////////////////////
  
  item_free(A);
  item_free(NA);
  item_free(B);
  item_free(NB2);
  item_free(NB22);
  item_free(B_S1);
  item_free(B_S2);
  
  network_disconnect(net_stat);
  network_disconnect(net_stat_serv);
  
  return KAB;
}

void receiver(int receiver, struct item *KBS)
  /*@ requires
        [?f0]world(nss_pub) &*&
        !bad(server_id()) &*& !bad(receiver) &*&
        generated_values(receiver, ?count) &*&
        item(KBS, ?kbs) &*& 
        kbs == key_item(receiver, 1, symmetric_key, int_pair(0, 0));
  @*/
  /*@  ensures
        [f0]world(nss_pub) &*&
        generated_values(receiver, ?count2) &*& count2 >= count &*&
        item(KBS, kbs);
  @*/
{
  struct network_status *net_stat = network_bind_and_accept(RECVER_PORT);
  
  // 1. A -> B. A
  int sender = 0;
  struct item *A = 0;
  {
    A = network_receive(net_stat);
    sender = item_get_data(A);
  }
  
  struct item* KAB = core_receiver(net_stat, sender, receiver, KBS);
  
  item_free(A);
  item_free(KAB);
  
  network_disconnect(net_stat);
}

struct item *core_receiver(struct network_status *net_stat, int sender, 
                           int receiver, struct item *KBS)
  /*@ requires
        [?f0]world(nss_pub) &*& network_status(net_stat) &*&
        !bad(server_id()) &*& !bad(receiver) &*&
        generated_values(receiver, ?count) &*&
        item(KBS, ?kbs) &*& 
        kbs == key_item(receiver, 1, symmetric_key, int_pair(0, 0));
  @*/
  /*@  ensures
        [f0]world(nss_pub) &*& network_status(net_stat) &*&
        generated_values(receiver, ?count2) &*& count2 >= count &*&
        item(KBS, kbs) &*& nss_pub(kbs) == false &*&
        item(result, ?kab) &*& kab == key_item(?p0, ?c0, ?k0, ?i0) &*&
        collision_in_run() ? 
          true 
        : 
          (
            p0 == server_id() &&
            k0 == symmetric_key &&
            i0 == int_pair(2, int_pair(sender, receiver))&&
            (bad(sender) || nss_pub(kab) == false)
          );
  @*/
{
  struct item *A = create_data_item(sender);
  struct item *B = create_data_item(receiver);
  
  // 2. B -> A. {A, NB1}_K(BS)
  struct item *NB1 = 0;
  {
    //@ close nonce_request(receiver, int_pair(3, sender));
    NB1 = create_nonce();                  //      NB1
    struct item *i1 = create_pair(A, NB1); //  (A, NB1)
    struct item *i2 = encrypt(KBS, i1);    // {(A, NB1)}_K(BS)
    network_send(net_stat, i2);
    item_free(i1);
    item_free(i2);
  }
  
  // 5. A -> B. {K(AB), A, NB1}_K(BS)
  struct item *KAB = 0;
  {
    struct item *i1 = network_receive(net_stat);
    struct item *i2 = decrypt(KBS, i1);    // (K(AB), (A, NB1))
    KAB = pair_get_first(i2);              //  K(AB)
    struct item *i3 = pair_get_second(i2); //         (A, NB1)
    struct item *i4 = pair_get_first(i3);  //          A
    struct item *i5 = pair_get_second(i3); //             NB1
      // check A
      if (!item_equals(i4, A)){abort();}
      // check NB1
      if (!item_equals(i5, NB1)){abort();}
      // check KAB
      check_is_key(KAB);
    item_free(i1);
    item_free(i2);
    item_free(i3);
    item_free(i4);
    item_free(i5);
  }
  
  //@ assert item(KAB, key_item(?p0, ?c0, ?k0, ?i0));
  //@ collision_in_run() ? true : p0 == 0;
  //@ collision_in_run() ? true : k0 == symmetric_key;
  //@ collision_in_run() ? true : i0 == int_pair(2, int_pair(sender, receiver));
  
  // 6. B -> A. {NB2, 0}_K(AB)
  struct item *NB2 = 0;
  {
    //@ close nonce_request(receiver, int_pair(5, sender));
    NB2 = create_nonce();
    struct item *i1 = create_data_item(0);  //        0
    struct item *i2 = create_pair(NB2, i1); //  (NB2, 0)
    struct item *i3 = encrypt(KAB, i2);     // {(NB2, 0)}_K(AB)
    network_send(net_stat, i3);
    item_free(i1);
    item_free(i2);
    item_free(i3);
  }
  
  // 7. A -> B. {NB2 + 1, 1}_K(AB)
  struct item *NB22 = 0;
  {
    NB22 = item_clone(NB2);
    increment_nonce(NB22); 
    struct item *i1 = network_receive(net_stat);
    struct item *i2 = decrypt(KAB, i1);        // (NB2 + 1, 1)
    struct item *i3 = pair_get_first(i2);      //  NB2 + 1
    struct item *i4 = pair_get_second(i2);     //           1
      int tag = item_get_data(i4);
      // check tag
      if (tag != 1){abort();}
      // check NB2 + 1
      if (!item_equals(NB22, i3)){abort();}
    item_free(i1);
    item_free(i2);
    item_free(i3);
    item_free(i4);
  }
  
    //Protocol End Goals
    ///////////////////////////////////////////////////////////////////////////
    //These goals are conditionally met: i.e. if the sender is not bad 
    //(otherwise the sender could leak the key or nonce)
    //
    //1) Secrecy of NB2
    //@  assert item(NB2, ?nb2);
    //@  assert bad(sender) || (nss_pub(nb2) == false);
    //
    //2) Secrecy of NB2 + 1
    //@  assert item(NB22, ?nb22);
    //@  assert bad(sender) || (nss_pub(nb22) == false);
    //
    //3) Secrecy of KBS
    //@  assert item(KBS, kbs);
    //@  assert (nss_pub(kbs) == false);
    //
    //4) Secrecy of KAB
    //@  assert item(KAB, ?kab);
    //@  assert  collision_in_run() ? true : (bad(sender) || (nss_pub(kab) == false));
    ///////////////////////////////////////////////////////////////////////////

  item_free(A);
  item_free(B);
  item_free(NB1);
  item_free(NB2);
  item_free(NB22);
  
  return KAB;
}

void server(int sender, int receiver, 
            struct item *KAS, struct item *KBS, struct item *KAB)
  /*@ requires [?f0]world(nss_pub) &*&
               !bad(server_id()) &*& !bad(sender) &*& !bad(receiver) &*&
               generated_values(server_id(), ?count1) &*&
               item(KAS, ?kas) &*& item(KBS, ?kbs) &*& item(KAB, ?kab) &*&
               kas == key_item(sender, 1, symmetric_key, int_pair(0,0)) &*&
               kbs == key_item(receiver, 1, symmetric_key, int_pair(0,0)) &*&
               kab == key_item(server_id(), ?count2, symmetric_key,
                                      int_pair(2,int_pair(sender, receiver)));
  @*/
  /*@ ensures  [f0]world(nss_pub) &*&
               generated_values(server_id(), ?count3) &*& count3 >= count1 &*&
               item(KAS, kas) &*& item(KBS, kbs) &*& item(KAB, kab);
  @*/
{ 
  struct network_status *net_stat  = network_bind_and_accept(SERVER_PORT);

  struct item *A = create_data_item(sender);
  struct item *B = create_data_item(receiver);
  
  // 3. A -> S. A, B, NA, {A, NB1}_K(BS)
  struct item *NA;
  struct item *NB1;
  {
    struct item *i1 = network_receive(net_stat); // A, B, NA, {A, NB1}_K(BS)
    struct item *i2 = pair_get_first(i1);        // A
      // check A
      if (!item_equals(i2, A)){abort();}
    struct item *i3 = pair_get_second(i1);       //    B, NA, {A, NB1}_K(BS)
    struct item *i4 = pair_get_first(i3);        //    B,
      // check B
      if (!item_equals(i4, B)){abort();}
    struct item *i5 = pair_get_second(i3);       //       NA, {A, NB1}_K(BS)
    NA = pair_get_first(i5);                     //       NA
      // check NA
      check_is_nonce(NA);
    struct item *i6 = pair_get_second(i5);       //          {A, NB1}_K(BS)
    struct item *i7 = decrypt(KBS, i6);          //           A, NB1
    struct item *i8 = pair_get_first(i7);        //           A
      // check A
      if (!item_equals(i8, A)){abort();}
    NB1 = pair_get_second(i7);                   //              NB1
      // check NB1
      check_is_nonce(NB1);
    item_free(i1);
    item_free(i3);
    item_free(i2);
    item_free(i4);
    item_free(i5);
    item_free(i6);
    item_free(i7);
    item_free(i8);
  }
  
  // 4. S -> A. {NA, K(AB), B, {K(AB), A, NB1}_K(BS)}_K(AS)
  {
    struct item *i1 = create_pair(A, NB1);
    struct item *i2 = create_pair(KAB, i1);
    struct item *i3 = encrypt(KBS, i2);
    struct item *i4 = create_pair(B, i3);
    struct item *i5 = create_pair(KAB, i4);
    struct item *i6 = create_pair(NA, i5);
    struct item *i7 = encrypt(KAS, i6);
    network_send(net_stat, i7);
    item_free(i1);
    item_free(i3);
    item_free(i2);
    item_free(i4);
    item_free(i5);
    item_free(i6);
    item_free(i7);
  }
  
  item_free(A);
  item_free(B);
  item_free(NA);
  item_free(NB1);
  
  network_disconnect(net_stat);
}
