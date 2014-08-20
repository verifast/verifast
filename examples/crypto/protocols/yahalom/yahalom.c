#include "yahalom.h"
#include "stdlib.h"

#define SERVER_PORT 343434
#define RECVER_PORT 232323
#define SENDER_PORT 121212

struct item *sender(int sender, int receiver, struct item *KAS)
  /*@ requires [?f0]world(yahalom_pub) &*&
               !bad(server_id()) &*& !bad(sender) &*& !bad(receiver) &*&
               generated_values(sender, ?count) &*& item(KAS, ?kas) &*&
               kas == key_item(sender, 1, symmetric_key, int_pair(0,0));
  @*/
  /*@ ensures  [f0]world(yahalom_pub) &*&
               generated_values(sender, ?count2) &*& count2 >= count &*&
               // Secrecy of KAS
               item(KAS, kas) &*& yahalom_pub(kas) == false &*&
               // Secrecy of KAB
               item(result, ?kab) &*& 
               kab == key_item(?p_ab, ?c_ab, ?k_ab, ?i_ab) &*&
               true == if_no_collision
               (
                 p_ab == server_id() &&
                 k_ab == symmetric_key &&
                 i_ab == int_pair(2, int_pair(sender, receiver)) &&
                 yahalom_pub(kab) == false
               );
  @*/
{
  struct network_status *net_stat_out = network_connect("localhost", RECVER_PORT);
  struct network_status *net_stat_in  = network_bind_and_accept(SENDER_PORT);
  
  struct item *i1;
  struct item *i2;
  struct item *i3;
  struct item *i4;
  struct item *i5;
  struct item *i6;
  struct item *i7;
  struct item *i8;
  
  struct item *A = create_data_item(sender);
  struct item *B = create_data_item(receiver);
  //@ close nonce_request(sender, int_pair(3, 0));
  struct item *NA = create_nonce();
  
  // 1. A -> B. A, NA
  i1 = create_pair(A, NA);
  network_send(net_stat_out, i1);
  item_free(i1);
  
  // 3. S -> A. {B, K(AB), NA, NB}_K(AS), {A, K(AB)}_K(BS)
  i1 = network_receive(net_stat_in);
  i2 = pair_get_first(i1);
  struct item *B_S = pair_get_second(i1);
  i3 = decrypt(KAS, i2);
  i4 = pair_get_first(i3); // B
    // check B
    if (!item_equals(i4, B)){abort();}
  i5 = pair_get_second(i3);
  struct item *KAB = pair_get_first(i5); // K(AB)
    // check KAB
    check_is_key(KAB);
  i6 = pair_get_second(i5);
  i7 = pair_get_first(i6); // NA
    // check NA
    if (!item_equals(i7, NA)){abort();}
  struct item *NB = pair_get_second(i6); // NB
    // check NB
    check_is_nonce(NB);
  item_free(i1);
  item_free(i2);
  item_free(i3);
  item_free(i4);
  item_free(i5);
  item_free(i6);
  item_free(i7);
  
  // 4. A -> B. {A, K(AB)}_K(BS), {NB}_K(AB)
  i1 = encrypt(KAB, NB);
  i2 = create_pair(B_S, i1);
  //@ SWITCH_CRYPTO_PRIMITIVES(i1, 1, 2);
 
  network_send(net_stat_out, i2);
  item_free(i1);
  item_free(i2);
  
    //Protocol End Goals
    ///////////////////////////////////////////////////////////////////////////
    //1) Secrecy of NB
    //@  assert item(NB, ?nb);
    //@  assert true == if_no_collision(!yahalom_pub(nb));
    //
    //2) Secrecy of KAS
    //@ assert item(KAS, kas);
    //@ assert true == if_no_collision(!yahalom_pub(kas));
    //
    //3) Secrecy of KAB
    //@ assert item(KAB, ?kab);
    //@ assert true == if_no_collision(!yahalom_pub(kab));
    ///////////////////////////////////////////////////////////////////////////

  item_free(A);
  item_free(B);
  item_free(NA);
  item_free(NB);
  item_free(B_S);
  
  network_disconnect(net_stat_in);
  network_disconnect(net_stat_out);
  
  return KAB;
}

void receiver(int receiver, struct item * KBS)
  /*@ requires [?f0]world(yahalom_pub) &*&
               !bad(server_id()) &*& !bad(receiver) &*&
               generated_values(receiver, ?count) &*& item(KBS, ?kbs) &*& 
               kbs == key_item(receiver, 1, symmetric_key, int_pair(0,0));
  @*/
  /*@ ensures  [f0]world(yahalom_pub) &*&
               generated_values(receiver, ?count2) &*& count2 >= count &*&
               item(KBS, kbs);
  @*/
{
  struct network_status *net_stat_in  = network_bind_and_accept(RECVER_PORT);
  struct network_status *net_stat_out = network_connect("localhost", SERVER_PORT);
  
  struct item *i1;
  
  // 1. A -> B. A, NA
  i1 = network_receive(net_stat_in);
  struct item *A = pair_get_first(i1);
  int sender = item_get_data(A);
  struct item *NA = pair_get_second(i1); // NA
    // check NA
    check_is_nonce(NA);
  item_free(i1);
  
  struct item* KAB = 
            core_receiver(net_stat_in, net_stat_out, sender, NA, receiver, KBS);
  
  item_free(A);
  item_free(KAB);
  
  network_disconnect(net_stat_in);
  network_disconnect(net_stat_out);
}
    
struct item *core_receiver(struct network_status *net_stat_in, 
                           struct network_status *net_stat_out, int sender, 
                           struct item* NA, int receiver, struct item * KBS)
  /*@ requires [?f0]world(yahalom_pub) &*&
               network_status(net_stat_in) &*& network_status(net_stat_out) &*&
               !bad(server_id()) &*& !bad(receiver) &*&
               generated_values(receiver, ?count) &*& item(KBS, ?kbs) &*&
               kbs == key_item(receiver, 1, symmetric_key, int_pair(0,0)) &*&
               item(NA, ?na) &*& true == if_no_collision(yahalom_pub(na));
  @*/
  /*@ ensures  [f0]world(yahalom_pub) &*&
               network_status(net_stat_in) &*& network_status(net_stat_out) &*&
               generated_values(receiver, ?count2) &*& count2 >= count &*& 
               item(KBS, kbs) &*& yahalom_pub(kbs) == false &*&
               item(result, ?kab) &*& 
               kab == key_item(?p_ab, ?c_ab, ?k_ab, ?i_ab) &*&
               true == if_no_collision(
                 p_ab == server_id() &&
                 k_ab == symmetric_key &&
                 i_ab == int_pair(2, int_pair(sender, receiver)) &&
                 bad(sender) || !yahalom_pub(kab)
               );
  @*/
{
  struct item *i1;
  struct item *i2;
  struct item *i3;
  struct item *i4;
  struct item *i5;
  struct item *i6;
  
  struct item *A = create_data_item(sender);
  struct item *B = create_data_item(receiver);
  
  // 2. B -> S. B, {A, NA, NB}_K(BS)
  //@ close nonce_request(receiver, int_pair(4, sender));
  struct item *NB = create_nonce();
  i1 = create_pair(NA, NB);
  i2 = create_pair(A, i1);
  i3 = encrypt(KBS, i2);
  i4 = create_pair(B, i3);
  network_send(net_stat_out, i4);
  item_free(i1);
  item_free(i2);
  item_free(i3);
  item_free(i4);
  
  // 4. A -> B. {A, K(AB)}_K(BS), {NB}_K(AB)
  i1 = network_receive(net_stat_in);
  i2 = pair_get_first(i1); // {A, K(AB)}_K(BS)
  i3 = pair_get_second(i1); // {NB}_K(AB)
  i4 = decrypt(KBS, i2);
  i5 = pair_get_first(i4); // A
    // check A
    if (!item_equals(i5, A)){abort();}
  struct item *KAB = pair_get_second(i4); // K(AB)
    // check KAB
    check_is_key(KAB);
  i6 = decrypt(KAB, i3); // NB
    // check NB
    if (!item_equals(i6, NB)){abort();}
  item_free(i1);
  item_free(i2);
  item_free(i3);
  item_free(i4);
  item_free(i5);
  item_free(i6);

    //Protocol End Goals
    ///////////////////////////////////////////////////////////////////////////
    //These goals are conditionally met: i.e. if the sender is not bad 
    //(otherwise the sender could leak the key or nonce)
    //
    //1) Secrecy of NB
    //@  assert item(NB, ?nb);
    //@  assert bad(sender) || !yahalom_pub(nb);
    //
    //2) Secrecy of KBS
    //@ assert item(KBS, kbs);
    //@ assert !yahalom_pub(kbs);
    //
    //3) Secrecy of KAB
    //@ assert item(KAB, ?kab);
    //@ assert true == if_no_collision(bad(sender) || !yahalom_pub(kab));
    ///////////////////////////////////////////////////////////////////////////
    
  item_free(A);
  item_free(B);
  item_free(NA);
  item_free(NB);
  
  return KAB;
}

void server(int sender, int receiver, struct item *KAS, struct item *KBS, struct item *KAB)
  /*@ requires [?f]world(yahalom_pub) &*&
               !bad(server_id()) &*& !bad(sender) &*& !bad(receiver) &*&
               generated_values(server_id(), ?count) &*&
               item(KAS, ?kas) &*& 
                 kas == key_item(sender, 1, symmetric_key, int_pair(0,0)) &*&
               item(KBS, ?kbs) &*& 
                 kbs == key_item(receiver, 1, symmetric_key, int_pair(0,0)) &*&
               item(KAB, ?kab) &*& 
                 kab == key_item(server_id(), 1, symmetric_key, 
                                 int_pair(2, int_pair(sender, receiver)));
  @*/
  /*@ ensures [f]world(yahalom_pub) &*&
              generated_values(server_id(), ?count2) &*& count2 >= count &*&
              item(KAS, kas) &*& item(KBS, kbs) &*& item(KAB, kab) &*&
              true == if_no_collision
              (
                yahalom_pub(kas) == false &&
                yahalom_pub(kbs) == false &&
                yahalom_pub(kab) == false
              );
  @*/
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
  
  struct item *A = create_data_item(sender);
  struct item *B = create_data_item(receiver);
  
  // 2. B -> S. B, {A, NA, NB}_K(BS)
  i1 = network_receive(net_stat_in);     // B, {A, NA, NB}_K(BS)
  i2 = pair_get_first(i1);               // B
    // check B
    if (!item_equals(i2, B)){abort();}
  i3 = pair_get_second(i1);              //    {A, NA, NB}_K(BS)
  i4 = decrypt(KBS, i3);                 //     A, NA, NB
  i5 = pair_get_first(i4);               //     A
    // check A
    if (!item_equals(i5, A)){abort();}
  i6 = pair_get_second(i4);              //        NA, NB
  struct item* NA = pair_get_first(i6);  //        NA
    // check NA
    check_is_nonce(NA);
  struct item* NB = pair_get_second(i6); //            NB
    // check NB
    check_is_nonce(NB);
  item_free(i1);
  item_free(i2);
  item_free(i3);
  item_free(i4);
  item_free(i5);
  item_free(i6);
  
  // 3. S -> A. {B, K(AB), NA, NB}_K(AS), {A, K(AB)}_K(BS)
  i1 = create_pair(A, KAB);
  i2 = encrypt(KBS, i1);
  i3 = create_pair(NA, NB);
  i4 = create_pair(KAB, i3);
  i5 = create_pair(B, i4);
  i6 = encrypt(KAS, i5);
  i7 = create_pair(i6, i2);
  
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
