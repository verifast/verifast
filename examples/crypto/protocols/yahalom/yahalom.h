#ifndef YAHALOM_H
#define YAHALOM_H

// See explanations in ../../include/cryptolib.h
#include "../../include/cryptolib.h"

/*

Dolev-Yao security verification of the Yahalom symmetric key protocol:

1. A -> B. A, NA
2. B -> S. B, {A, NA, NB}_K(BS)
3. S -> A. {B, K(AB), NA, NB}_K(AS), {A, K(AB)}_K(BS)
4. A -> B. {A, K(AB)}_K(BS), {NB}_K(AB)

Goal: A and B share a symmetric encryption session key K(AB)

*/

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*
Encodings for this protocol
key_item:
  *For communication by participant A with the trusted server:
     sender == A &*& info == int_pair(0, 0)
  *For communication by participant A with participant B:
     sender == 0 &*& info == int_pair(2, int_pair(A, B))
info for messages:
  *Encryption:
    int_pair(0, 0) : for communication with the trusted key server
    int_pair(2, int_pair(A, B)) : for communication bewteen two principals
  *Nonces:
    int_pair(3, 0): NA
    int_pair(4, A): NB
*/

/*@

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint int server_id() {return 1;}

fixpoint bool yahalom_pub(item i)
{
  switch (i)
  {
    case data_item(data0):
      // A & B
      return true;
    case pair_item(first0, second0):
      // For concatenation (Concatenations of public items are public)
      return yahalom_pub(first0) && yahalom_pub(second0);
    case nonce_item(p0, count0, inc0, info0):
      // NA & NB (NB should remain secret)
      return
        bad(p0) ||
        int_left(info0) == 3 ||
        int_left(info0) == 4 && 
          (
            bad(server_id()) ||                  // Trusted server S leaks key NB
            bad(int_right(info0))                // Participant A leaks key NB
          );
    case key_item(p0, count0, kind0, info0):
      // K(AS) & K(BS) & K(AB) (Keys should not leak)
      return
        bad(p0) ||                               // Creator leaks the key
        // Only symmetric encryption in this protocol
        kind0 == symmetric_key && 
        (
          int_left(info0) == 2 && 
            (
              bad(int_left(int_right(info0))) || // Participant A leaks key KAB
              bad(int_right(int_right(info0)))   // Participant B leaks key KAB  
            )
        );
    case hmac_item(key0, payload0): return
      switch(key0)
      {
        case key_item(p1, count1, kind1, info1):
          return yahalom_pub(key0);
        default: return false;
      };
    case encrypted_item(key0, pay0, entropy0): return
      switch(key0)
      {
        case key_item(p1, count1, kind1, info1): return 
          yahalom_pub(key0) && yahalom_pub(pay0)
          ||
          // Only symmetric encryption in this protocol
          kind1 == symmetric_key && 
          switch(pay0)
          {
            case nonce_item(p2, count2, inc2, info2): return
              // {NB}_K(AB)
              p1 == server_id() &&
              int_left(info1) == 2 &&
              int_right(int_right(info1)) == p2 &&
              int_left(int_right(info1)) == int_right(info2) &&
              int_left(info2) == 4;
            case pair_item(first1, second1): return
              switch(second1)
              {
                case key_item(p2, count2, kind2, info2): return
                  switch(first1)
                  {
                    case data_item(data3): return    
                      // {A, K(AB)}_K(BS)
                      p1 == int_right(int_right(info2)) &&
                      info1 == int_pair(0, 0) &&
                      p2 == server_id() &&
                      kind2 == symmetric_key &&
                      info2 == int_pair(2, int_pair(data3, p1));
                    default: return false;
                  };
                case pair_item(first2, second2): return
                  switch(second2)
                  {
                    case nonce_item(p3, count3, inc3, info3): return // NB
                      switch(first1)
                      {
                        case data_item(data4): return // A
                          //{A, NA, NB}_K(BS)
                          p1 == p3 &&
                          info1 == int_pair(0, 0) &&
                          info3 == int_pair(4, data4) &&
                          //no info yet about NA
                          yahalom_pub(first2);
                        default: return false;
                      };
                    case pair_item(first3, second3): return
                      switch(second3)
                      {
                        case nonce_item(p4, count4, inc4, info4): return //NB
                          switch(first1)
                            {
                              case data_item(data5): return //B
                                switch(first2)
                                {
                                  case key_item(p6, count6, kind6, info6): return //K(AB)
                                    // {B, K(AB), NA, NB}_K(AS)
                                    p1 == int_left(int_right(info6)) &&
                                    info1 == int_pair(0, 0) &&
                                    p4 == data5 &&
                                    info4 == int_pair(4, p1) &&
                                    p6 == server_id() &&
                                    kind6 == symmetric_key &&
                                    info6 == int_pair(2, int_pair(p1, data5)) &&
                                    //no info yet about NA
                                    yahalom_pub(first3);
                                  default: return false;
                                };
                              default: return false;
                            };
                        default: return false;
                      };
                    default: return false;
                  };
                default: return false;
              };
            default: return false;
          };
        default: return false;
      };
    default: return false;
  }
}

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *sender(int sender, int receiver, struct item *KAS);
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

void receiver(int receiver, struct item * KBS);
  /*@ requires [?f0]world(yahalom_pub) &*&
               !bad(server_id()) &*& !bad(receiver) &*&
               generated_values(receiver, ?count) &*& item(KBS, ?kbs) &*& 
               kbs == key_item(receiver, 1, symmetric_key, int_pair(0,0));
  @*/
  /*@ ensures  [f0]world(yahalom_pub) &*&
               generated_values(receiver, ?count2) &*& count2 >= count &*&
               item(KBS, kbs);
  @*/

struct item *core_receiver(struct network_status *net_stat_in,
                           struct network_status *net_stat_out, int sender,
                           struct item* NA, int receiver, struct item * KBS);
  /*@ requires [?f0]world(yahalom_pub) &*&
               network_status(net_stat_in) &*& network_status(net_stat_out) &*&
               !bad(server_id()) &*& !bad(receiver) &*&
               generated_values(receiver, ?count) &*& 
               item(KBS, ?kbs) &*&
               kbs == key_item(receiver, 1, symmetric_key, int_pair(0,0)) &*&
               item(NA, ?na) &*& true == if_no_collision(yahalom_pub(na));
  @*/
  /*@ ensures  [f0]world(yahalom_pub) &*&
               network_status(net_stat_in) &*& network_status(net_stat_out) &*&
               generated_values(receiver, ?count2) &*& count2 >= count &*&
               item(KBS, kbs) &*&
               yahalom_pub(kbs) == false &*&
               item(result, ?kab) &*&
               kab == key_item(?p_ab, ?c_ab, ?k_ab, ?i_ab) &*&
               true == if_no_collision(
                 p_ab == server_id() &&
                 k_ab == symmetric_key &&
                 i_ab == int_pair(2, int_pair(sender, receiver)) &&
                 bad(sender) || !yahalom_pub(kab)
               );
  @*/

void server(int sender, int receiver, struct item *KAS, struct item *KBS, struct item *KAB);
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

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
  DEFAULT_CAN_SEND_DATA(yahalom)
  DEFAULT_CAN_SEND_PUBLIC_PAIR(yahalom)
  DEFAULT_CAN_SEND_DECOMPOSED_PUBLIC_PAIR(yahalom)
  DEFAULT_CAN_SEND_BAD_PRINCIPAL_NONCE(yahalom)
  DEFAULT_CAN_SEND_INCREMENTED_NONCE(yahalom)
  DEFAULT_CAN_SEND_BAD_PRINCIPAL_KEYS(yahalom)
  DEFAULT_CAN_SEND_PUBLIC_HMAC(yahalom)
  DEFAULT_CAN_SEND_PUBLIC_ENCRYPTED(yahalom)
  DEPTH_CAN_SEND_PUBLIC_DECRYPTED(yahalom, 4)
@*/

#endif
