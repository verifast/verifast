#ifndef NSS_H
#define NSS_H

// See explanations in ../../lib/dolevyao.h
#include "dolevyao.h"

/*

Dolev-Yao security verification of the Needham-Schroeder symmetric key protocol:

1. A -> B. A
2. B -> A. {A, NB1}_K(BS)
3. A -> S. A, B, NA, {A, NB1}_K(BS)
4. S -> A. {NA, K(AB), B, {K(AB), A, NB1}_K(BS)}_K(AS)
5. A -> B. {K(AB), A, NB1}_K(BS)
6. B -> A. {NB2, 0}_K(AB)
7. A -> B. {NB2 + 1, 1}_K(AB)  
           // The original protocol does not send 0 & 1 back and forth. 
           // This is done to be able to distinguish the two different messages.

Goal: A and B share a symmetric encryption session key K(AB)

*/

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*
key_item:
  *For communication by participant A with the trusted server:
     creator == A &*& info == int_pair(1, 0)
  *For communication by participant A with participant B:
     creator == 0 &*& info == int_pair(2, int_pair(A, B))

info for messages:
  *Encryption:
    int_pair(1, 0)              : for (possibly indirect) communication with 
                                  the trusted key server
    int_pair(2, int_pair(A, B)) : for communication bewteen two principals
  *Nonces:
    int_pair(3, A): NB1
    int_pair(4, B): NA
    int_pair(5, A): NB2
    int_pair(6, int_pair(5, A)): NB2 + 1
*/

/*@

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

// A definition of "pub" for the example protocol.
fixpoint bool nss_pub(item i) 
{
  switch (i) 
  {
    case pair_item(first0, second0):
      // For concatenation (Concatenations of public items are public)
      return nss_pub(first0) && nss_pub(second0);
    case nonce_item(p0, count0, info0):
      // e.g. NA is public, NB1, NB2 and NB2 + 1 should remain secret
      return 
        bad(p0) || 
        int_left(info0) == 3 && bad(int_right(info0)) || // NB1
        int_left(info0) == 4 ||                          // NA
        int_left(info0) == 5 && bad(int_right(info0)) || // NB2
        int_left(info0) == 6 &&                          // NB2 + 1
          int_left(int_right(info0)) == 5 && 
          bad(int_right(int_right(info0)));
    case key_item(s0, count0, kind0, info0):
      // Should not happen
      return 
        (bad(s0) ||                // Creator leaks the key
         int_left(info0) == 2 && 
           (bad(int_left(int_right(info0))) || // Participant A leaks key KAB
            bad(int_right(int_right(info0))))  // Participant B leaks key KAB
        );
    case hmac_item(s0, count0, kind0, info0, payload):
      // Should not happen
      return 
        (bad(s0) ||                // Creator leaks the key
         int_left(info0) == 2 && 
           (bad(int_left(int_right(info0))) || // Participant A leaks key KAB
            bad(int_right(int_right(info0))))  // Participant B leaks key KAB
        );
    case data_item(data0):
      // e.g. A or B
      return true;
    case encrypted_item(s0, count0, kind0, info0, p0, entropy0): return 
      nss_pub(p0) && 
        (bad(s0) || 
         int_left(info0) == 2 &&
           (bad(int_right(int_right(info0))) || 
            bad(int_left(int_right(info0)))
           )
        ) ||
      kind0 == symmetric_key && // Only symmetric encryption in this protocol
      switch(p0)
      {
        case pair_item(first1, second1): return 
          switch(second1)
          {
            case data_item(d2): return
              switch(first1)
              {
                case nonce_item(s3, count3, info3): return
                  s0 == 0 &&
                  int_left(info0) == 2 &&
                  int_right(int_right(info0)) == s3 && // B
                  (
                    d2 == 0 && // {NB2, 0}_K(AB)
                      int_left(info3) == 5 &&
                      int_left(int_right(info0)) == int_right(info3)
                    ||
                    d2 == 1 && // {NB2 + 1, 1}_K(AB)
                      int_left(info3) == 6 &&
                      int_left(int_right(info3)) == 5 &&
                      int_left(int_right(info0)) == int_right(int_right(info3)) // A
                  );
                default: return false;
              };
            case nonce_item(s2, count2, info2): return
              info0 == int_pair(0, 0) && 
              switch(first1)
              {
                // {A, NB1}_K(BS)
                case data_item(s3): return
                  s0 == s2 &&
                  info2 == int_pair(3, s3);
                default: return false;
              };
            case pair_item(first2, second2): return
              info0 == int_pair(0, 0) && 
              switch(second2)
              {
                case nonce_item(s3, count3, info3): return
                  switch(first1)
                  {
                    case key_item(s4, count4, kind4, info4): return
                      switch(first2)
                      { 
                        //{K(AB), A, NB1}_K(BS)
                        case data_item(d5): return
                          s0 == s3 &&                 // B
                          info4 == int_pair(2, int_pair(d5, s0)) && 
                          s4 == 0 &&                  
                          kind4 == symmetric_key;
                        default: return false;
                      };
                    default: return false;
                  };
                  //{NA, K(AB), B, {K(AB), A, NB1}_K(BS)}_K(AS)
                case pair_item(first3, second3): return
                  nss_pub(second3) && // {K(AB), A, NB1}_K(BS)
                  switch(first1)
                  {
                    case nonce_item(s4, count4, info4): return
                      switch(first2)
                      {
                        case key_item(s5, count5, kind5, info5): return
                          switch(first3)
                          { 
                            case data_item(d6): return
                              nss_pub(first1) &&
                              s5 == 0 &&
                              kind5 == symmetric_key &&
                              info5 == int_pair(2, int_pair(s0, d6));
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

//@ predicate protocol_pub(; fixpoint(item, bool) pub);

void init_protocol();
  //@ requires true;
  //@ ensures protocol_pub(nss_pub) &*& generated_keys(0, ?count);

///////////////////////////////////////////////////////////////////////////////
// Protocol implementation ////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *sender(int sender, int receiver, struct item * KAS);
  /*@ requires 
        [?f0]world(nss_pub) &*&
        !bad(sender) &*& !bad(receiver) &*& !bad(0) &*&
        generated_nonces(sender, ?count) &*& 
        key_item(KAS, sender, 0, symmetric_key, int_pair(0, 0));
  @*/
  /*@ ensures 
        [f0]world(nss_pub) &*&
        generated_nonces(sender, count + 1) &*&
        key_item(KAS, sender, 0, symmetric_key, int_pair(0, 0)) &*&
        key_item(result, 0, ?cab, symmetric_key, 
                                  int_pair(2, int_pair(sender, receiver))) &*&
        // Secrecy of KAS
        nss_pub(key_item(sender, 0, symmetric_key, int_pair(0, 0))) == false &*&
        // Secrecy of KAB
        nss_pub(key_item(0, cab, symmetric_key, 
                            int_pair(2, int_pair(sender, receiver)))) == false; 
  @*/

void receiver(int receiver, struct item *KBS);
  /*@ requires 
        [?f0]world(nss_pub) &*&
        !bad(receiver) &*& !bad(0) &*&
        generated_nonces(receiver, ?count) &*& 
        key_item(KBS, receiver, 0, symmetric_key, int_pair(0, 0));
  @*/
  /*@  ensures 
        [f0]world(nss_pub) &*&
        generated_nonces(receiver, count + 2) &*&
        key_item(KBS, receiver, 0, symmetric_key, int_pair(0, 0)); 
  @*/

struct item *core_receiver(struct network_status *net_stat, int sender, 
                           int receiver, struct item *KBS);
  /*@ requires 
        [?f0]world(nss_pub) &*& network_status(net_stat) &*&
        !bad(receiver) &*& !bad(0) &*&
        generated_nonces(receiver, ?count) &*& 
        key_item(KBS, receiver, 0, symmetric_key, int_pair(0, 0));
  @*/
  /*@  ensures 
        [f0]world(nss_pub) &*& network_status(net_stat) &*&
        generated_nonces(receiver, count + 2) &*&
        key_item(KBS, receiver, 0, symmetric_key, int_pair(0, 0)) &*&
        key_item(result, 0, ?cab, symmetric_key, 
                                  int_pair(2, int_pair(sender, receiver))) &*&
        // Secrecy of KBS
        nss_pub(key_item(receiver, 0, symmetric_key, int_pair(0, 0))) == false &*&
        // Secrecy (conditionally on sender being bad) of KAB
        (bad(sender) || nss_pub(key_item(0, cab, symmetric_key, 
                            int_pair(2, int_pair(sender, receiver)))) == false); 
  @*/

void server(int sender, int receiver, struct item *KAS, 
                                            struct item *KBS, struct item *KAB);
  /*@ requires [?f0]world(nss_pub) &*&
               !bad(0) &*& !bad(sender) &*& !bad(receiver) &*&
               key_item(KAS, sender, 0, symmetric_key, int_pair(0,0)) &*&
               key_item(KBS, receiver, 0, symmetric_key, int_pair(0,0)) &*&
               item(KAB, key_item(0, ?count, symmetric_key, 
                                      int_pair(2,int_pair(sender, receiver))));
  @*/
  /*@ ensures [f0]world(nss_pub) &*&
              key_item(KAS, sender, 0, symmetric_key, int_pair(0,0)) &*&
              key_item(KBS, receiver, 0, symmetric_key, int_pair(0,0)) &*&
              item(KAB, key_item(0, count, symmetric_key, 
                                      int_pair(2,int_pair(sender, receiver))));
  @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
DEFAULT_CAN_SEND_BAD_PRINCIPAL_KEYS(nss)
DEFAULT_CAN_SEND_DATA(nss)
DEFAULT_CAN_SEND_PUBLIC_PAIR(nss)
DEFAULT_CAN_SEND_DECOMPOSED_PUBLIC_PAIR(nss)
DEFAULT_CAN_SEND_PUBLIC_ENCRYPTED(nss)
DEPTH_CAN_SEND_PUBLIC_DECRYPTED(nss, 4)
DEFAULT_CAN_SEND_PUBLIC_HMAC(nss)
@*/

#endif