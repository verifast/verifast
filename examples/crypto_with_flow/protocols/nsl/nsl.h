#ifndef NSL_H
#define NSL_H

#include "../../annotated_api/polarssl_definitions/polarssl_definitions.h"

#define NONCE_SIZE 8

#define KEY_SIZE 128

/*@

// 1. A -> B. {A,NA}_K(B)
// 2. B -> A. {B,NA,NB}_K(A)
// 3. A -> B. {NB}_K(B)

//or

// 1. sender -> receiver : ASYM_ENC(K(receiver),
//                           {NAME(sender), NONCE(sender)})
// 2. receiver -> sender : ASYM_ENC(K(sender),
//                           {NAME(receiver), NONCE(sender), NONCE(receiver)})
// 3. sender -> receiver : ASYM_ENC(K(receiver),
//                           {NONCE(receiver)})

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

// info:
//  int_pair(1, receiver): sender nonce
//  int_pair(2, int_pair(sender, p_instigator)): receiver nonce

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint bool nsl_public_nonce(int principal, int info)
{
  return
    collision_in_run ||
    bad(principal) ||
    (int_left(info) == 1 && bad(int_right(info))) ||
    (int_left(info) == 2 && bad(int_left(int_right(info))));
}

predicate nsl_pub_msg_sender(int receiver) = true;

predicate nsl_pub_msg1(int sender, int receiver, cryptogram s_nonce) = true;

predicate nsl_pub_msg2(int p_instigator, int sender, int receiver, 
                       list<char> s_nonce_cs, cryptogram r_nonce) = true;

predicate nsl_pub_msg3(int sender, int receiver, cryptogram r_nonce) = true;

predicate nsl_proof_pred() =
  exists(?attacker) &*& true == bad(attacker)
;

predicate nsl_pub(cryptogram cg) =
  switch (cg)
  {
    case cg_random(p0, c0):
      return true == nsl_public_nonce(p0, cg_info(cg));
    case cg_symmetric_key(p0, c0):
      return true == bad(p0);
    case cg_public_key(p0, c0):
      return true;
    case cg_private_key(p0, c0):
      return true == bad(p0);
    case cg_hash(cs0):
      return true;
    case cg_hmac(p0, c0, cs0):
      return true;
    case cg_encrypted(p0, c0, cs0, ent0):
      return true == bad(p0) &*& [_]public_generated(nsl_pub)(cs0);
    case cg_auth_encrypted(p0, c0, mac0, cs0, ent0):
      return true == bad(p0) &*& [_]public_generated(nsl_pub)(cs0);
    case cg_asym_encrypted(p0, c0, cs0, ent0):
      return [_]nsl_pub_msg_sender(?p1) &*& 
      collision_in_run || bad(p0) || bad(p1) ?
        [_]public_generated(nsl_pub)(cs0)
      : 
      (
        length(cs0) == 4 + NONCE_SIZE ?
        (
          // 1. A -> B. {A,NA}_K(B)
          nsl_pub_msg1(?sender, ?receiver, ?s_nonce) &*&
          p1 == sender && p0 == receiver &*&
          cs0 == append(chars_of_int(sender), chars_for_cg(s_nonce)) &*&
          length(chars_of_int(sender)) == 4 &*&
          s_nonce == cg_random(sender, _) &*&
          cg_info(s_nonce) == int_pair(1, receiver) &*&
          true == cg_is_generated(s_nonce) &*&
          [_]public_generated(nsl_pub)(take(4, cs0))
        )
      : length(cs0) == 4 + 2 * NONCE_SIZE ?
          // 2. B -> A. {B,NA,NB}_K(A)
          nsl_pub_msg2(?p_instigator, ?sendr, ?receiver,
                       ?s_nonce_cs, ?r_nonce) &*&
          p1 == receiver && p0 == sendr &*&
          r_nonce == cg_random(receiver, _) &*&
          cs0 == append(chars_of_int(receiver),
                        append(s_nonce_cs,
                               chars_for_cg(r_nonce))) &*&
          cg_info(r_nonce) == int_pair(2, int_pair(sendr, p_instigator)) &*&
          true == cg_is_generated(r_nonce) &*&
          length(s_nonce_cs) == NONCE_SIZE &*&
          length(chars_of_int(receiver)) == 4 &*&
          [_]public_generated(nsl_pub)(take(4, cs0)) &*&
          bad(p_instigator) ?
            [_]public_generated(nsl_pub)(s_nonce_cs)
          :
            p_instigator == sendr
      : length(cs0) == NONCE_SIZE ?
          // 3. A -> B. {NB}_K(B)
          nsl_pub_msg3(?sender, ?receiver, ?r_nonce) &*&
          p1 == sender &*& p0 == receiver &*&
          r_nonce == cg_random(receiver, _) &*&
          cs0 == chars_for_cg(r_nonce) &*&
          cg_info(r_nonce) == int_pair(2, int_pair(sender, sender)) &*&
          true == cg_is_generated(r_nonce) &*&
          length(cs0) == NONCE_SIZE
      :
          false
      ); 
    case cg_asym_signature(p0, c0, cs0, ent0):
      return true == bad(p0);
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void sender(int sender, int receiver, 
            char *s_priv_key, char *r_pub_key,
            char *s_nonce, char *r_nonce);
/*@ requires [_]public_invar(nsl_pub) &*&
             principal(sender, _) &*&
             [?f1]cryptogram(s_priv_key, 8 * KEY_SIZE,
                             ?s_priv_key_cs, ?s_priv_key_cg) &*&
               s_priv_key_cg == cg_private_key(sender, ?s_id) &*&
             [?f2]cryptogram(r_pub_key, 8 * KEY_SIZE,
                             ?r_pub_key_cs, ?r_pub_key_cg) &*&
               r_pub_key_cg == cg_public_key(receiver, ?r_id) &*&
             chars(s_nonce, NONCE_SIZE, _) &*&
             chars(r_nonce, NONCE_SIZE, _); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(s_priv_key, 8 * KEY_SIZE,
                            s_priv_key_cs, s_priv_key_cg) &*&
             [f2]cryptogram(r_pub_key, 8 * KEY_SIZE,
                            r_pub_key_cs, r_pub_key_cg) &*&
             cryptogram(s_nonce, NONCE_SIZE, ?s_nonce_cs, ?s_nonce_cg) &*&
               s_nonce_cg == cg_random(sender, _) &*&
               cg_info(s_nonce_cg) == int_pair(1, receiver) &*&
             collision_in_run || bad(sender) || bad(receiver) ?
               chars(r_nonce, NONCE_SIZE, _)
             :
               cryptogram(r_nonce, NONCE_SIZE, _, ?r_nonce_cg) &*&
               r_nonce_cg == cg_random(receiver, _) &*&
               cg_info(r_nonce_cg) == int_pair(2, int_pair(sender, sender)); @*/

void receiver(int sender, int receiver, 
              char *s_pub_key, char *r_priv_key,
              char *s_nonce, char *r_nonce);
/*@ requires [_]public_invar(nsl_pub) &*&
             principal(receiver, _) &*&
             [?f1]cryptogram(s_pub_key, 8 * KEY_SIZE,
                             ?s_pub_key_cs, ?s_pub_key_cg) &*&
               s_pub_key_cg == cg_public_key(sender, ?s_id) &*&
             [?f2]cryptogram(r_priv_key, 8 * KEY_SIZE, 
                             ?r_priv_key_cs, ?r_priv_key_cg) &*&
               r_priv_key_cg == cg_private_key(receiver, ?r_id) &*&
             chars(s_nonce, NONCE_SIZE, _) &*&
             chars(r_nonce, NONCE_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(s_pub_key, 8 * KEY_SIZE,
                            s_pub_key_cs, s_pub_key_cg) &*&
             [f2]cryptogram(r_priv_key, 8 * KEY_SIZE,
                            r_priv_key_cs, r_priv_key_cg) &*&
             cryptogram(r_nonce, NONCE_SIZE, ?r_nonce_cs, ?r_nonce_cg) &*&
               r_nonce_cg == cg_random(receiver, _) &*&
             (
               collision_in_run || bad(sender) || bad(receiver) ?
                 chars(s_nonce, NONCE_SIZE, _)
               :
                 cryptogram(s_nonce, NONCE_SIZE, ?s_nonce_cs, ?s_nonce_cg) &*&
                 s_nonce_cg == cg_random(sender, _) &*&
                 cg_info(s_nonce_cg) == int_pair(1, receiver) &*&
                 cg_info(r_nonce_cg) == int_pair(2, int_pair(sender, sender))   
             ); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@ 
DEFAULT_IS_PUBLIC_RANDOM(nsl)
DEFAULT_IS_PUBLIC_KEY(nsl)
DEFAULT_IS_PUBLIC_PUBLIC_KEY(nsl)
DEFAULT_IS_PUBLIC_PRIVATE_KEY(nsl)
DEFAULT_IS_PUBLIC_HASH(nsl)
DEFAULT_IS_PUBLIC_HMAC(nsl)
DEFAULT_IS_PUBLIC_ENCRYPTED(nsl)
DEFAULT_IS_PUBLIC_DECRYPTED(nsl)
DEFAULT_IS_PUBLIC_AUTH_ENCRYPTED(nsl)
DEFAULT_IS_PUBLIC_AUTH_DECRYPTED(nsl)
// DEFAULT_IS_PUBLIC_ASYMMETRIC_ENCRYPTED(nsl)
// DEFAULT_IS_PUBLIC_ASYMMETRIC_DECRYPTED(nsl)
DEFAULT_IS_PUBLIC_ASYMMETRIC_SIGNATURE(nsl)

lemma void public_asym_encryption_is_public(cryptogram encrypted)
  requires nsl_proof_pred() &*&
           encrypted == cg_asym_encrypted(?p, ?c, ?pay, ?ent) &*&
           [_]nsl_pub(cg_public_key(p, c)) &*&
           [_]public_generated(nsl_pub)(pay);
  ensures  nsl_proof_pred() &*&
           [_]nsl_pub(encrypted);
{
  open  [_]nsl_pub(cg_public_key(p, c));
  POLARSSL_SWITCH_1(PREFIX, cg_public_key(p, c));
  open nsl_proof_pred();
  assert exists(?attacker);
  close nsl_proof_pred();
  close nsl_pub_msg_sender(attacker);
  leak nsl_pub_msg_sender(attacker);
  close nsl_pub(encrypted);
  leak nsl_pub(encrypted);
}

lemma void public_asym_decryption_is_public(cryptogram key,
                                            cryptogram encrypted)
  requires key == cg_private_key(?p, ?c) &*&
           encrypted == cg_asym_encrypted(p, c, ?pay, ?ent) &*&
           [_]nsl_pub(key) &*&
           [_]nsl_pub(encrypted);
  ensures  [_]public_generated(nsl_pub)(pay);
{
  open  [_]nsl_pub(key);
  open  [_]nsl_pub(encrypted);
  
  POLARSSL_SWITCH_1(PREFIX, cg_private_key(p, c));
  assert true == bad(p);
}

@*/

#endif
