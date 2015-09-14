#ifndef ENC_THEN_HMAC_H
#define ENC_THEN_HMAC_H

#include "../../annotated_api/polarssl_definitions/polarssl_definitions.h"

#define MAX_SIZE 1024
#define KEY_SIZE 32

/*@

// 1. sender -> receiver : {ENC(K1, M), HMAC(K2, ENC(K1, M))}

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint int shared_with(int sender, int id);
fixpoint bool send(int sender, int receiver, list<char> message);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate enc_then_hmac_proof_pred() = true;

predicate enc_then_hmac_pub_1(int p, list<char> cs1, list<char> cs2) = true;

predicate enc_then_hmac_pub(cryptogram cg) =
  switch (cg)
  {
    case cg_random(p0, c0):
      return true;
    case cg_symmetric_key(p0, c0):
      return true == bad(p0);
    case cg_public_key(p0, c0):
      return true;
    case cg_private_key(p0, c0):
      return true == bad(p0);
    case cg_hash(cs0):
      return true;
    case cg_hmac(p0, c0, cs0):
      return bad(p0) || bad(shared_with(p0, c0)) ? 
        true 
      :
        enc_then_hmac_pub_1(?c1, ?cs1, ?ent1) &*&
        length(ent1) == 20 &&
        cs0 == append(ent1, chars_for_cg(cg_encrypted(p0, c1, cs1, ent1))) &&
        shared_with(p0, c0) == shared_with(p0, c1) &&
        send(p0, shared_with(p0, c0), cs1);
    case cg_encrypted(p0, c0, cs0, ent0):
      return bad(p0) || bad(shared_with(p0, c0)) ?
        [_]public_generated(enc_then_hmac_pub)(cs0)
      : 
        true == send(p0, shared_with(p0, c0), cs0);
    case cg_auth_encrypted(p0, c0, mac0, cs0, ent0):
      return [_]public_generated(enc_then_hmac_pub)(cs0) &*&
             (bad(p0) || bad(shared_with(p0, c0)));
    case cg_asym_encrypted(p0, c0, cs0, ent0):
      return [_]public_generated(enc_then_hmac_pub)(cs0);
    case cg_asym_signature(p0, c0, cs0, ent0):
      return true == bad(p0);
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void sender(char *enc_key, char *hmac_key, char *msg, unsigned int msg_len);
/*@ requires [_]public_invar(enc_then_hmac_pub) &*&
             principal(?sender, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_cs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_cs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               shared_with(sender, enc_id) == shared_with(sender, hmac_id) &*&
             [?f3]crypto_chars(msg, msg_len, ?msg_cs) &*&
               MAX_SIZE >= msg_len &*& msg_len >= MIN_ENC_SIZE &*&
               bad(sender) || bad(shared_with(sender, enc_id)) ?
                 [_]public_generated(enc_then_hmac_pub)(msg_cs)
               :
                 // Not saying anything about publicness of msg_cs established 
                 // confidentiality
                 true == send(sender, shared_with(sender, enc_id), msg_cs); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(enc_key, KEY_SIZE, enc_key_cs, enc_key_cg) &*&
             [f2]cryptogram(hmac_key, KEY_SIZE, hmac_key_cs, hmac_key_cg) &*&
             [f3]crypto_chars(msg, msg_len, msg_cs); @*/

int receiver(char *enc_key, char *hmac_key, char *msg);
/*@ requires [_]public_invar(enc_then_hmac_pub) &*&
             principal(?receiver, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_cs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_cs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(?sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               receiver == shared_with(sender, enc_id) &*&
               receiver == shared_with(sender, hmac_id) &*&
             chars(msg, MAX_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(enc_key, KEY_SIZE, enc_key_cs, enc_key_cg) &*&
             [f2]cryptogram(hmac_key, KEY_SIZE, hmac_key_cs, hmac_key_cg) &*&
             chars(msg + result, MAX_SIZE - result, _) &*&
             crypto_chars(msg, result, ?msg_cs) &*&
             bad(sender) || bad(receiver) || collision_in_run() ||
             send(sender, receiver, msg_cs); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PUBLIC_INVARIANT_PROOFS(enc_then_hmac)

#endif
