#ifndef YAHALOM_H
#define YAHALOM_H

// See explanations in ../../lib/dolevyao.h
#include "dolevyao.h"
#include "attacker.h"

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
     sender == A &*& info == int_pair(2, int_pair(A, B))
info for messages:
  *Encryption:
    int_pair(0, 0) : for communication with the trusted key server
    int_pair(2, int_pair(A, B)) : for communication bewteen two principals
  *Nonces:
    int_pair(3, 0): NA
    int_pair(4, int_pair(A, B)): NB
*/

/*@

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint bool yahalom_pub(item i) 
{
  switch (i) 
  {
    case pair_item(first0, second0):
      // For concatenation (Concatenations of public items are public)
      return yahalom_pub(first0) && yahalom_pub(second0);
    case nonce_item(p0, count0, info0):
      // NA & NB (NB should remain secret)
      return info0 == int_pair(3, 0) || 
             bad(p0) ||
             bad(int_left(int_right(info0))) ||
             bad(int_right(int_right(info0)));
    case key_item(s0, count0, kind0, info0):
      // K(AS) & K(BS) & K(AB) (Keys should not leak)
      return bad(s0) || bad(int_right(info0));
    case hmac_item(s0, count0, kind0, info0, payload0):
      return bad(s0) || bad(int_right(info0));
    case data_item(data0):
      // A & B
      return true;
    case encrypted_item(s0, count0, kind0, info0, p0, entropy0): return
      ((bad(s0) || bad(int_right(info0))) && yahalom_pub(p0)) ||
      switch(p0)
      {
        // {NB}_K(AB)
        case nonce_item(s1, count1, info1): return 
          kind0 == symmetric_key &&
          info0 == int_pair(2, s1) &&
          info1 == int_pair(4, int_pair(s0, s1));
        case pair_item(first1, second1): return
          switch(second1)
          {
            // {A, K(AB)}_K(BS)
            case key_item(s2, count2, kind2, info2): return
              s0 == int_right(info2) &&
              info0 == int_pair(0, 0) &&
              kind0 == symmetric_key &&
              first1 == data_item(s2) &&
              info2 == int_pair(2, s0) &&
              kind2 == symmetric_key;
            case pair_item(first2, second2): return
              switch(second2)
              {
                //{A, NA, NB}_K(BS)
                case nonce_item(s3, count3, info3): return // NB
                  switch(first1)
                  {
                    case data_item(data4): return // A
                      switch(first2)
                      {
                        case nonce_item(s5, count5, info5): return // NA
                          s0 == s3 &&
                          info0 == int_pair(0, 0) &&
                          kind0 == symmetric_key &&
                          // B cannot know this for sure
                          // data4 == s5 &&
                          info3 == int_pair(4, int_pair(data4, s3)) &&
                          (info5 == int_pair(3, 0) || 
                          bad(s5) ||
                          bad(int_left(int_right(info5))) ||
                          bad(int_right(int_right(info5))));
                        default: return false;
                      };
                    default: return false;
                  };
                // {B, K(AB), NA, NB}_K(AS)
                case pair_item(first3, second3): return
                  switch(second3)
                  {
                    case nonce_item(s4, count4, info4): return //NB
                      switch(first1)
                        {
                          case data_item(data5): return //B
                            switch(first2)
                            {
                              case key_item(s6, count6, kind6, info6): return //K(AB)
                                switch(first3)
                                {   
                                  case nonce_item(s7, count7, info7): return //NA
                                    s0 == s6 &&
                                    info0 == int_pair(0, 0) &&
                                    kind0 == symmetric_key &&
                                    info6 == int_pair(2, data5) &&
                                    kind6 == symmetric_key &&
                                      // S cannot know this for sure
                                      // s7 == s6 &&
                                    (info7 == int_pair(3, 0) || 
                                     bad(s7) ||
                                     bad(int_left(int_right(info7))) ||
                                     bad(int_right(int_right(info7)))) &&
                                    s4 == data5 &&
                                    info4 == int_pair(4, int_pair(s6, data5));
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

/*@ 
predicate protocol_pub(; fixpoint(item, bool) pub);

lemma void init_protocol();
     requires true;
     ensures protocol_pub(yahalom_pub);
@*/

struct item *sender(int sender, int receiver, struct item *KAS);
  /*@ requires !bad(sender) &*& !bad(receiver) &*& !bad(0) &*&
               [?f]world(yahalom_pub) &*& 
               generated_nonces(sender, ?count) &*& 
               key_item(KAS, sender, 0, symmetric_key, int_pair(0,0)); 
  @*/
  /*@ ensures  [f]world(yahalom_pub) &*&
               generated_nonces(sender, count + 1) &*& 
               key_item(KAS, sender, 0, symmetric_key, int_pair(0,0)) &*& 
               // Secrecy of KAS
               yahalom_pub(key_item(sender, 0, symmetric_key, 
                             int_pair(0, 0))) == false &*&
               key_item(result, sender, ?cab, symmetric_key, 
                             int_pair(2, receiver)) &*&
               // Secrecy of KAB
               yahalom_pub(key_item(sender, cab, symmetric_key, 
                             int_pair(2, receiver))) == false; 
  @*/

void receiver(int receiver, struct item * KBS);
  /*@ requires !bad(receiver) &*& !bad(0) &*&
               [?f]world(yahalom_pub) &*& 
               generated_nonces(receiver, ?count) &*&
               key_item(KBS, receiver, 0, symmetric_key, int_pair(0,0)); 
  @*/
  /*@ ensures  [f]world(yahalom_pub) &*& 
               generated_nonces(receiver, count + 1) &*& 
               key_item(KBS, receiver, 0, symmetric_key, int_pair(0,0)); 
  @*/

struct item *core_receiver(struct network_status *net_stat_in, 
                           struct network_status *net_stat_out, int sender, 
                           struct item* NA, int receiver, struct item * KBS);
  /*@ requires !bad(receiver) &*& !bad(0) &*&
               [?f]world(yahalom_pub) &*& 
               generated_nonces(receiver, ?count) &*&
               key_item(KBS, receiver, 0, symmetric_key, int_pair(0,0)) &*&
               item(NA, nonce_item(?p, ?c, ?i)) &*& 
               yahalom_pub(nonce_item(p, c, i)) == true; 
  @*/
  /*@ ensures  [f]world(yahalom_pub) &*& 
               generated_nonces(receiver, count + 1) &*& 
               key_item(KBS, receiver, 0, symmetric_key, int_pair(0,0)) &*&
               // Secrecy of KBS
               yahalom_pub(key_item(receiver, 0, symmetric_key, 
                             int_pair(0, 0))) == false &*&
               key_item(result, sender, ?cab, symmetric_key, 
                             int_pair(2, receiver)) &*&
               // Secrecy of KAB
               bad(sender) || yahalom_pub(key_item(sender, cab, symmetric_key, 
                             int_pair(2, receiver))) == false; 
  @*/

void server(int sender, int receiver, struct item *KAS, struct item *KBS, struct item *KAB);
  /*@ requires [?f]world(yahalom_pub) &*&
               !bad(0) &*& !bad(sender) &*& !bad(receiver) &*&
               key_item(KAS, sender, 0, symmetric_key, int_pair(0,0)) &*&
               key_item(KBS, receiver, 0, symmetric_key, int_pair(0,0)) &*&
               item(KAB, key_item(sender, ?count, symmetric_key, int_pair(2,receiver)));
  @*/
  /*@ ensures [f]world(yahalom_pub) &*&
              key_item(KAS, sender, 0, symmetric_key, int_pair(0,0)) &*&
              key_item(KBS, receiver, 0, symmetric_key, int_pair(0,0)) &*&
              item(KAB, key_item(sender, count, symmetric_key, int_pair(2,receiver)));
  @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
DEFAULT_CAN_SEND_BAD_PRINCIPAL_KEYS(yahalom)
DEFAULT_CAN_SEND_DATA(yahalom)
DEFAULT_CAN_SEND_PUBLIC_PAIR(yahalom)
DEFAULT_CAN_SEND_DECOMPOSED_PUBLIC_PAIR(yahalom)
DEFAULT_CAN_SEND_PUBLIC_ENCRYPTED(yahalom)
DEPTH_CAN_SEND_PUBLIC_DECRYPTED(yahalom, 4)
DEFAULT_CAN_SEND_PUBLIC_HMAC(yahalom)
@*/

#endif