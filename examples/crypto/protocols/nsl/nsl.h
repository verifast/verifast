#ifndef NSL_H
#define NSL_H

// See explanations in ../../include/cryptolib.h
#include "../../include/cryptolib.h"

/*

Dolev-Yao security verification of the Needham-Schroeder-Lowe public key
authentication protocol:

1. A -> B. {A,NA}_K(B)
2. B -> A. {B,NA,NB}_K(A)
3. A -> B. {NB}_K(B)

Goal: Secrets NA and NB shared between A and B

Client: A
Server: B 

*/

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*
info:
  int_pair(0, 0): for encryption
  int_pair(1, receiver): sender nonce
  int_pair(2, int_pair(sender, receiver)): receiver nonce
*/

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
// A definition of "pub" for the example protocol.
fixpoint bool nsl_public_nonce(int principal, int info)
{
  return
    bad(principal) ||
    (int_left(info) == 1 && bad(int_right(info))) ||
    (int_left(info) == 2 && bad(int_left(int_right(info))));
}

predicate nsl_pub(item i) =
  collision_in_run() ? true :
  [_]info_for_item(i, ?info0) &*&
  switch (i) 
  {
    case data_item(d0):
      return true;
    case pair_item(f0, s0):
      return [_]nsl_pub(f0) &*& 
             [_]nsl_pub(s0);
    case nonce_item(p0, c0, inc0): 
      return true == nsl_public_nonce(p0, info0);
    case hash_item(pay0): return
      switch (pay0)
      {
        case some(pay1):
          return [_]nsl_pub(pay1);
        case none:
          return true;
      };
    case symmetric_key_item(p0, c0):
      return true == bad(p0);
    case public_key_item(p0, c0):
      return true;
    case private_key_item(p0, c0):
      return true == bad(p0);
    case hmac_item(p0, c0, pay0): 
      return true;
    case symmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1):
          return [_]nsl_pub(pay1);
        case none:
          return true;
      };
    case asymmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1): return
          [_]message_tag(i)(?tag) &*& 
          tag == 10 ?
          (
            [_]nsl_pub(pay1)
          ) :
          tag == 12 ?
          (
            !bad(p0) &*& 
            pay0 == some(pay1) &*&
            pay1 == pair_item(data_item(cons(?p1, nil)), ?nonce) &*&
            nonce == nonce_item(p1, _, 0) &*&
            [_]info_for_item(nonce, int_pair(1, p0))
          ) :
          tag == 13 ?
          (
            !bad(p0) &*& 
            pay0 == some(pay1) &*&
            pay1 == pair_item(data_item(cons(?p1, nil)), ?pair1) &*&
            pair1 == pair_item(?nonce1, ?nonce2) &*&
            [_]info_for_item(nonce1, int_pair(1, p1)) &*&
            nonce1 == nonce_item(p0, _, 0) &*&
            [_]info_for_item(nonce2, int_pair(2, int_pair(p0, p1))) &*&
            nonce2 == nonce_item(p1, _, 0)
          ) :
          tag == 14 ?
          (
            !bad(p0) &*&
            pay1 == nonce_item(?p1, _, 0) &*&
            [_]info_for_item(pay1, ?info1) &*&
            int_left(info1) == 2 &*&
            int_right(int_right(info1)) == p1 &*&
            (!bad(p1) ? true : int_left(int_right(info1)) == p0)
          ) :
          false;
        case none:
          return true;
      };
    case asymmetric_signature_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay0_): return bad(p0) ? 
              [_]nsl_pub(pay0_) 
            : 
              [_]message_tag(i)(?tag) &*& 
              tag == 21 ?
              (
                pay0_ == hash_item(some(?pay1_)) &*&
                pay1_ == pair_item(data_item(cons(?p1, nil)), ?key) &*&
                key == public_key_item(p1, 1)
              ) :
              tag == 22 ?
              (
                pay0_ == pair_item(data_item(cons(?p1, nil)), ?hash1) &*&
                hash1 == hash_item(some(?enc1)) &*&
                enc1 == asymmetric_encrypted_item(p1, 1, some(?pay1), _) &*&
                pay1 == pair_item(data_item(cons(p0, nil)), ?nonce1) &*&
                [_]info_for_item(nonce1, int_pair(1, p1)) &*&
                nonce1 == nonce_item(p0, _, 0)
              ) :
              tag == 23 ?
              (
                pay0_ == pair_item(data_item(cons(?p1, nil)), ?hash1) &*&
                hash1 == hash_item(some(?enc1)) &*&
                enc1 == asymmetric_encrypted_item(p1, 1, some(?pay1), _) &*&
                pay1 == pair_item(data_item(cons(p0, nil)), ?pair1) &*&
                pair1 == pair_item(?nonce1, ?nonce2) &*&
                (
                  bad(p1) ? 
                    true
                  :
                    [_]info_for_item(nonce1, int_pair(1, p0)) &*&
                    nonce1 == nonce_item(p1, _, 0) &*&
                    [_]info_for_item(nonce2, int_pair(2, int_pair(p1, p0))) &*&
                    nonce2 == nonce_item(p0, _, 0)   
                )
              ) :
              tag == 24 ?
              (
                pay0_ == pair_item(data_item(cons(?p1, nil)), ?hash1) &*&
                hash1 == hash_item(some(?enc1)) &*&
                enc1 == asymmetric_encrypted_item(p1, 1, some(?pay1), _) &*&
                pay1 == nonce_item(p1, _, 0) &*&
                [_]info_for_item(pay1, int_pair(2, int_pair(p0, p1)))
              ) :
              false;
        case none:
          return true;
      };
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void server(char server, struct item *KS_PRIVATE);
  /*@ requires [?f0]world(nsl_pub) &*&
               generated_values(server, _) &*&
               !bad(server) &*&
               item(KS_PRIVATE, ?ksp, nsl_pub) &*& 
                 ksp == private_key_item(server, 1); @*/
  /*@ ensures  [f0]world(nsl_pub) &*&
               generated_values(server, _) &*&
               item(KS_PRIVATE, ksp, nsl_pub); @*/

void sender(char sender, char receiver, char server,
            struct item *KA_PRIVATE, struct item *KS,
            struct item **NA, struct item **NB);
  /*@ requires [?f0]world(nsl_pub) &*&
               generated_values(sender, _) &*& 
               !bad(sender) &*& !bad(receiver) &*& !bad(server) &*&
               item(KA_PRIVATE, ?kap, nsl_pub) &*& 
                 kap == private_key_item(sender, 1) &*&
               item(KS, ?ks, nsl_pub) &*&
                 ks == public_key_item(server, 1) &*&
               pointer(NA, _) &*& pointer(NB, _); @*/
  /*@ ensures  [f0]world(nsl_pub) &*&
               generated_values(sender, _) &*&
               item(KA_PRIVATE, kap, nsl_pub) &*& 
               item(KS, ks, nsl_pub) &*&
               pointer(NA, ?nap) &*& pointer(NB, ?nbp) &*&
               item(nap, ?na, nsl_pub) &*&
                 [_]info_for_item(na, ?i_na) &*&
               item(nbp, ?nb, nsl_pub) &*&
                 [_]info_for_item(nb, ?i_nb) &*&
               collision_in_run() ?
                 true
               :
                 // Secrecy of NA
                 na == nonce_item(sender, _, 0) &*&
                 i_na == int_pair(1, receiver) &*&
                 is_not_public(_, nsl_pub, na, i_na) &*&
                 // Secrecy of NB
                 nb == nonce_item(receiver, _, 0) &*&
                 i_nb == int_pair(2, int_pair(sender, receiver)) &*&
                 is_not_public(_, nsl_pub, nb, i_nb); @*/

int receiver(char receiver, char server, 
             struct item *KB_PRIVATE, struct item *KS,
             struct item **NA, struct item **NB);
  /*@ requires [?f0]world(nsl_pub) &*&
               generated_values(receiver, _) &*& 
               !bad(receiver) &*& !bad(server) &*&
               item(KB_PRIVATE, ?kbp, nsl_pub) &*&
                 kbp == private_key_item(receiver, 1) &*&
               item(KS, ?ks, nsl_pub) &*&
                 ks == public_key_item(server, 1) &*&
               pointer(NA, _) &*& pointer(NB, _); @*/
  /*@ ensures  [f0]world(nsl_pub) &*&
               generated_values(receiver, _) &*& !bad(receiver) &*&
               item(KB_PRIVATE, kbp, nsl_pub) &*&
               item(KS, ks, nsl_pub)&*&
               pointer(NA, ?nap) &*& pointer(NB, ?nbp) &*&
               item(nbp, ?nb, nsl_pub) &*&
                 [_]info_for_item(nb, ?i_nb) &*&
               item(nap, ?na, nsl_pub) &*&
                 [_]info_for_item(na, ?i_na) &*&
               collision_in_run() || bad(result) ?
                 true
               :
                 // Secrecy of NB
                 nb == nonce_item(receiver, _, 0) &*&
                 i_nb == int_pair(2, int_pair(result, receiver)) &*&
                 is_not_public(_, nsl_pub, nb, i_nb) &*&
                 // Secrecy of NA
                 na == nonce_item(result, _, 0) &*&
                 i_na == int_pair(1, receiver) &*&
                 is_not_public(_, nsl_pub, na, i_na); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PROOFS_DEFAULT(nsl)

#endif
