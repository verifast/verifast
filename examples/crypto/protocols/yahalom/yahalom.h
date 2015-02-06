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
Encodings for this protocol (info for items):
  *Nonces:
    int_pair(0, 0): NA
    int_pair(1, A): NB
  *Encryption:
    int_pair(2, 0)              : for communication with the trusted key server
    int_pair(3, int_pair(A, B)) : for communication bewteen two principals
*/

/*@

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint int server_id() {return 2;}

fixpoint bool yahalom_public_nonce(int principal, int info)
{
  return
    // Random nonce
    bad(principal) ||        // Bad creator leaks the nonce
    // NA
    int_left(info) == 0 ||   // Nonce NA is public
    // NB
    int_left(info) == 1 && 
      (
        bad(server_id()) ||  // Trusted server S leaks nonce NB
        bad(int_right(info)) // Participant A leaks nonce NB
      )
  ; 
}

fixpoint bool yahalom_public_key(int principal, int info)
{
  return 
    // Random key
    bad(principal) ||                     // Bad creator leaks the key
    // KAB
    int_left(info) == 3 && 
      (
        bad(int_left(int_right(info))) || // Participant A leaks key KAB
        bad(int_right(int_right(info)))   // Participant B leaks key KAB  
      )
  ;
}

predicate yahalom_pub(item i) =
  collision_in_run() ? true :
  [_]info_for_item(i, ?info0) &*&
  switch (i)
  {
    case data_item(data0):
      return true;
    case pair_item(first0, second0):
      return [_]yahalom_pub(first0) &*& 
             [_]yahalom_pub(second0);
    case nonce_item(p0, count0, inc0):
      return true == yahalom_public_nonce(p0, info0);
    case hash_item(pay0): return
      switch (pay0)
      {
        case some(pay1):
          return [_]yahalom_pub(pay1);
        case none:
          return true;
      };
    case symmetric_key_item(p0, count0):
      return true == yahalom_public_key(p0, info0);
    case public_key_item(p0, c0):
      return true;
    case private_key_item(p0, c0):
      return true == bad(p0);
    case hmac_item(p0, c0, pay0): return
      switch (pay0)
      {
        case none:
          return true;
        case some(pay1):
          return [_]yahalom_pub(pay1);
      };
    case symmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch(pay0)
      {
        case none:
          return true;
        case some(pay1):
          return true == yahalom_public_key(p0, info0) ?
            [_]yahalom_pub(pay1)
          :
            switch(pay1)
            {
              case nonce_item(p2, count2, inc2): return
                // {NB}_K(AB)
                [_]info_for_item(pay1, ?info2) &*&
                p0 == server_id() &*&
                int_left(info2) == 1 &*&
                int_right(info2) == int_left(int_right(info0)) &*&
                int_left(info0) == 3 &*&
                int_right(int_right(info0)) == p2;
              case pair_item(first1, second1): return
                switch(second1)
                {
                  case symmetric_key_item(p2, count2): return
                    [_]info_for_item(second1, ?info2) &*&
                    switch(first1)
                    {
                      case data_item(data3): return    
                        // {A, K(AB)}_K(BS)
                        info0 == int_pair(2, 0) &*&
                        p2 == server_id() &*&
                        data3 == cons(?data3_, nil) &*&
                        info2 == int_pair(3, int_pair(data3_, p0));
                      case pair_item(f3, s3): return false;
                      case nonce_item(p3, c3, inc3): return false;
                      case hash_item(pay3): return false;
                      case symmetric_key_item(p3, c3): return false;
                      case public_key_item(p3, c3): return false;
                      case private_key_item(p3, c3): return false;
                      case hmac_item(p3, c3, pay3): return false;
                      case symmetric_encrypted_item(p3, c3, pay3, ent3): return false;
                      case asymmetric_encrypted_item(p3, c3, pay3, ent3): return false;
                      case asymmetric_signature_item(p3, c3, pay3, ent3): return false;
                    };
                  case pair_item(first2, second2): return
                    switch(second2)
                    {
                      case nonce_item(p3, count3, inc3): return // NB
                        [_]info_for_item(second2, ?info3) &*&
                        switch(first1)
                        {
                          case data_item(data4): return // A
                            //{A, NA, NB}_K(BS)
                            info0 == int_pair(2, 0) &*&
                            p0 == p3 &*&
                            data4 == cons(?data4_, nil) &*&
                            info3 == int_pair(1, data4_) &*&
                            //no info yet about NA
                            [_]yahalom_pub(first2);
                          case pair_item(f4, s4): return false;
                          case nonce_item(p4, c4, inc4): return false;
                          case hash_item(pay4): return false;
                          case symmetric_key_item(p4, c4): return false;
                          case public_key_item(p4, c4): return false;
                          case private_key_item(p4, c4): return false;
                          case hmac_item(p4, c4, pay4): return false;
                          case symmetric_encrypted_item(p4, c4, pay4, ent4): return false;
                          case asymmetric_encrypted_item(p4, c4, pay4, ent4): return false;
                          case asymmetric_signature_item(p4, c4, pay4, ent4): return false;
                        };
                      case pair_item(first3, second3): return
                        switch(second3)
                        {
                          case nonce_item(p4, count4, inc4): return //NB
                            [_]info_for_item(second3, ?info4) &*&
                            switch(first1)
                              {
                                case data_item(data5): return //B
                                  switch(first2)
                                  {
                                    case symmetric_key_item(p6, count6): return //K(AB)
                                      [_]info_for_item(first2, ?info6) &*&
                                      // {B, K(AB), NA, NB}_K(AS)
                                      info0 == int_pair(2, 0) &*&
                                      data5 == cons(?data5_, nil) &*&
                                      p4 == data5_ &*&
                                      p6 == server_id() &*&
                                      info6 == int_pair(3, int_pair(p0, data5_)) &*&
                                      info4 == int_pair(1, p0) &*&
                                      //no info yet about NA
                                      [_]yahalom_pub(first3);
                                    case data_item(d6): return false;
                                    case pair_item(f6, s6): return false;
                                    case nonce_item(p6, c6, inc6): return false;
                                    case hash_item(pay6): return false;
                                    case public_key_item(p6, c6): return false;
                                    case private_key_item(p6, c6): return false;
                                    case hmac_item(p6, c6, pay6): return false;
                                    case symmetric_encrypted_item(p6, c6, pay6, ent6): return false;
                                    case asymmetric_encrypted_item(p6, c6, pay6, ent6): return false;
                                    case asymmetric_signature_item(p6, c6, pay6, ent6): return false;
                                  };
                                case pair_item(f5, s5): return false;
                                case nonce_item(p5, c5, inc5): return false;
                                case hash_item(pay5): return false;
                                case symmetric_key_item(p5, c5): return false;
                                case public_key_item(p5, c5): return false;
                                case private_key_item(p5, c5): return false;
                                case hmac_item(p5, c5, pay5): return false;
                                case symmetric_encrypted_item(p5, c5, pay5, ent5): return false;
                                case asymmetric_encrypted_item(p5, c5, pay5, ent5): return false;
                                case asymmetric_signature_item(p5, c5, pay5, ent5): return false;
                              };
                          case data_item(d4): return false;
                          case pair_item(f4, s4): return false;
                          case hash_item(pay4): return false;
                          case symmetric_key_item(p4, c4): return false;
                          case public_key_item(p4, c4): return false;
                          case private_key_item(p4, c4): return false;
                          case hmac_item(p4, c4, pay4): return false;
                          case symmetric_encrypted_item(p4, c4, pay4, ent4): return false;
                          case asymmetric_encrypted_item(p4, c4, pay4, ent4): return false;
                          case asymmetric_signature_item(p4, c4, pay4, ent4): return false;
                        };
                      case data_item(d3): return false;
                      case hash_item(pay3): return false;
                      case symmetric_key_item(p3, c3): return false;
                      case public_key_item(p3, c3): return false;
                      case private_key_item(p3, c3): return false;
                      case hmac_item(p3, c3, pay3): return false;
                      case symmetric_encrypted_item(p3, c3, pay3, ent3): return false;
                      case asymmetric_encrypted_item(p3, c3, pay3, ent3): return false;
                      case asymmetric_signature_item(p3, c3, pay3, ent3): return false;
                    };
                  case data_item(d2): return false;
                  case nonce_item(p2, c2, inc2): return false;
                  case hash_item(pay2): return false;
                  case public_key_item(p2, c2): return false;
                  case private_key_item(p2, c2): return false;
                  case hmac_item(p2, c2, pay2): return false;
                  case symmetric_encrypted_item(p2, c2, pay2, ent2): return false;
                  case asymmetric_encrypted_item(p2, c2, pay2, ent2): return false;
                  case asymmetric_signature_item(p2, c2, pay2, ent2): return false;
                };
              case data_item(d1): return false;
              case hash_item(pay11): return false;
              case symmetric_key_item(p1, c1): return false;
              case public_key_item(p1, c1): return false;
              case private_key_item(p1, c1): return false;
              case hmac_item(p1, c1, pay11): return false;
              case symmetric_encrypted_item(p1, c1, pay11, ent1): return false;
              case asymmetric_encrypted_item(p1, c1, pay11, ent1): return false;
              case asymmetric_signature_item(p1, c1, pay11, ent1): return false;
            };
      };
    case asymmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1): return
          [_]message_tag(i)(?tag) &*& 
          tag == 10 ?
          (
            [_]yahalom_pub(pay1)
          ) :
          false;
        case none:
          return true;
      };
    case asymmetric_signature_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1):
          return [_]yahalom_pub(pay1);
        case none:
          return true;
      };
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *sender(char sender, char receiver, struct item *KAS);
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

void receiver(char receiver, struct item * KBS);
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

struct item *core_receiver(struct network_status *net_stat_in,
                           struct network_status *net_stat_out, char sender,
                           struct item* NA, char receiver, struct item * KBS);
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

void server(char sender, char receiver, struct item *KAS, 
            struct item *KBS, struct item *KAB);
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

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PROOFS_DEFAULT(yahalom)

#endif
