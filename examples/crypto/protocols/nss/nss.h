#ifndef NSS_H
#define NSS_H

// See explanations in ../../include/lib/cryptolib.h
#include "../../include/cryptolib.h"

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
     creator == A           &*& info == int_pair(0, 0)
  *For communication by participant B with the trusted server:
     creator == B           &*& info == int_pair(0, 0)
  *For communication by participant A with participant B:
     creator == server_id() &*& info == int_pair(2, int_pair(A, B))

info for messages:
  *Encryption:
    int_pair(0, 0)              : for (possibly indirect) communication with
                                  the trusted key server
    int_pair(2, int_pair(A, B)) : for communication bewteen two principals
  *Nonces:
    int_pair(3, A): NB1
    int_pair(4, B): NA
    int_pair(5, A): NB2
*/

/*@

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint int server_id() {return 1;}

// A definition of "pub" for the example protocol.
fixpoint bool nss_pub(item i)
{
  switch (i)
  {
    case data_item(data0):
      // e.g. A or B
      return true;
    case pair_item(first0, second0):
      // For concatenation (Concatenations of public items are public)
      return nss_pub(first0) && nss_pub(second0);
    case nonce_item(p0, count0, inc0, info0):
      // e.g. NA is public, NB1, NB2 and NB2 + 1 should remain secret
      return
        bad(server_id()) || bad(p0) ||
          int_left(info0) == 3 && bad(int_right(info0)) || // NB1
          int_left(info0) == 4 ||                          // NA
          int_left(info0) == 5 && bad(int_right(info0));   // NB2 & NB2 + 1;
    case key_item(p0, count0, kind0, info0):
      // Should not happen
      return
        (bad(p0) ||                            // Creator leaks the key
         int_left(info0) == 2 &&
           (bad(int_left(int_right(info0))) || // Participant A leaks key KAB
            bad(int_right(int_right(info0))))  // Participant B leaks key KAB
        );
    case hmac_item(key0, pay0): return
      // Should not happen
      switch (key0)
      {
        case key_item(p1, count1, kind1, info1):
          return nss_pub(key0);
        default: return false;
      };
    case encrypted_item(key0, pay0, entropy0): return
      switch (key0)
      {
        case key_item(p1, count1, kind1, info1):
          return 
            nss_pub(key0) && nss_pub(pay0)
            ||
            // Only symmetric encryption in this protocol
            kind1 == symmetric_key && 
            switch(pay0)
            {
              case pair_item(first1, second1): return
                switch(second1)
                {
                  case data_item(d2): return
                    switch(first1)
                    {
                      // {NB2, 0}_K(AB)
                      // {NB2 + 1, 1}_K(AB)
                      case nonce_item(p3, count3, inc3, info3): return
                        p1 == server_id() &&
                        info1 == int_pair(2, int_pair(int_right(info3), p3)) &&
                        int_left(info3) == 5 &&
                        (
                          d2 == 0 && inc3 == 0 ||
                          d2 == 1 && inc3 == 1
                        );
                      default: return false;
                    };
                  case nonce_item(p2, count2, inc2, info2): return
                    switch(first1)
                    {
                      // {A, NB1}_K(BS)
                      case data_item(d3): return
                        p1 == p2 &&
                        info1 == int_pair(0, 0) &&
                        inc2 == 0 &&
                        info2 == int_pair(3, d3);
                      default: return false;
                    };
                  case pair_item(first2, second2): return
                    switch(second2)
                    {
                      case nonce_item(p3, count3, inc3, info3): return
                        switch(first1)
                        {
                          case key_item(p4, count4, kind4, info4): return
                            switch(first2)
                            { 
                              //{K(AB), A, NB1}_K(BS)
                              case data_item(d5): return
                                p1 == p3 &&
                                info1 == int_pair(0, 0) &&
                                inc3 == 0 &&
                                info3 == int_pair(3, d5) &&
                                p4 == server_id() &&
                                kind4 == symmetric_key &&
                                info4 == int_pair(2, int_pair(d5, p1));
                              default: return false;
                            };
                          default: return false;
                        };
                      case pair_item(first3, second3): return
                        //{NA, K(AB), B, {K(AB), A, NB1}_K(BS)}_K(AS)
                        
                        switch(first1)
                        {
                          case nonce_item(s4, count4, inc4, info4): return
                            switch(first2)
                            {
                              case key_item(s5, count5, kind5, info5): return
                                switch(first3)
                                {
                                  case data_item(d6): return
                                    info1 == int_pair(0, 0) &&
                                    nss_pub(first1) &&  // NA
                                    s5 == server_id() &&
                                    kind5 == symmetric_key &&
                                    info5 == int_pair(2, int_pair(p1, d6)) &&
                                    nss_pub(second3);  // {K(AB), A, NB1}_K(BS)
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
  }
}

@*/

///////////////////////////////////////////////////////////////////////////////
// Protocol implementation ////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *sender(int sender, int receiver, struct item * KAS);
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

void receiver(int receiver, struct item *KBS);
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

struct item *core_receiver(struct network_status *net_stat, int sender,
                           int receiver, struct item *KBS);
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
            i0 == int_pair(2, int_pair(sender, receiver)) &&
            (bad(sender) || nss_pub(kab) == false)
          );
  @*/

void server(int sender, int receiver, 
            struct item *KAS, struct item *KBS, struct item *KAB);
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

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
  DEFAULT_CAN_SEND_DATA(nss)
  DEFAULT_CAN_SEND_PUBLIC_PAIR(nss)
  DEFAULT_CAN_SEND_DECOMPOSED_PUBLIC_PAIR(nss)
  DEFAULT_CAN_SEND_BAD_PRINCIPAL_NONCE(nss)
  DEFAULT_CAN_SEND_INCREMENTED_NONCE(nss)
  DEFAULT_CAN_SEND_BAD_PRINCIPAL_KEYS(nss)
  DEFAULT_CAN_SEND_PUBLIC_HMAC(nss)
  DEFAULT_CAN_SEND_PUBLIC_ENCRYPTED(nss)
  DEPTH_CAN_SEND_PUBLIC_DECRYPTED(nss, 4)
@*/

#endif
