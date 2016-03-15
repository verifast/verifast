#ifndef HMAC_THEN_ENC_NESTED_H
#define HMAC_THEN_ENC_NESTED_H

#include "../../annotated_api/polarssl_definitions/polarssl_definitions.h"

#define MAX_SIZE 1024
#define KEY_SIZE 32

/*@

// 1. sender -> receiver : ENC(K1, {M, HMAC(K2, M)})

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint int shared_with(int sender, int id);
fixpoint bool send(int sender, int receiver, list<char> message);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate hmac_then_enc_nested_proof_pred() = true;

predicate hmac_then_enc_nested_pub_1(cryptogram inner_enc, list<char> cs, 
                                     cryptogram hmac) = true;

fixpoint bool hmac_then_enc_nested_public_key(int p, int c, bool symmetric)
{
  return symmetric ?
           bad(p) || bad(shared_with(p, c))
         :
           bad(p);
}

predicate hmac_then_enc_nested_pub(cryptogram cg) =
  switch (cg)
  {
    case cg_nonce(p0, c0):
      return true;
    case cg_symmetric_key(p0, c0):
      return true == hmac_then_enc_nested_public_key(p0, c0, true);
    case cg_public_key(p0, c0):
      return true;
    case cg_private_key(p0, c0):
      return true == hmac_then_enc_nested_public_key(p0, c0, false);
    case cg_hash(cs0):
      return true;
    case cg_hmac(p0, c0, cs0):
      return true;
    case cg_encrypted(p0, c0, cs0, ent0):
      return hmac_then_enc_nested_public_key(p0, c0, true) ?
        [_]public_generated(hmac_then_enc_nested_pub)(cs0)
      :
        hmac_then_enc_nested_pub_1(?enc_cg, ?msg_cs, ?hmac_cg) &*&
        cs0 == chars_for_cg(enc_cg) &*&
        enc_cg == cg_encrypted(p0, ?c1, ?cs1, _) &*&
        true == cg_is_generated(enc_cg) &*&
        cs1 == append(msg_cs, chars_for_cg(hmac_cg)) &*&
        true == cg_is_generated(hmac_cg) &*&
        length(chars_for_cg(hmac_cg)) == 64 &*&
        hmac_cg == cg_hmac(p0, ?c2, msg_cs) &*&
        cg_info(cg_symmetric_key(p0, c0)) == c2 &*&
        cg_info(cg_symmetric_key(p0, c1)) == c2 &*&
        shared_with(p0, c0) == shared_with(p0, c1) &*&
        shared_with(p0, c0) == shared_with(p0, c2) &*&
        true == send(p0, shared_with(p0, c0), msg_cs);
    case cg_auth_encrypted(p0, c0, cs0, ent0):
      return true == hmac_then_enc_nested_public_key(p0, c0, true) &*&
             [_]public_generated(hmac_then_enc_nested_pub)(cs0);
    case cg_asym_encrypted(p0, c0, cs0, ent0):
      return [_]public_generated(hmac_then_enc_nested_pub)(cs0);
    case cg_asym_signature(p0, c0, cs0, ent0):
      return true == hmac_then_enc_nested_public_key(p0, c0, false);
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void sender(char *enc_key1, char *enc_key2, char *hmac_key, 
            char *msg, unsigned int msg_len);
/*@ requires [_]public_invar(hmac_then_enc_nested_pub) &*&
             principal(?sender, _) &*&
             [?f1]cryptogram(enc_key1, KEY_SIZE, ?enc_key_cs1, ?enc_key_cg1) &*&
             [?f2]cryptogram(enc_key2, KEY_SIZE, ?enc_key_cs2, ?enc_key_cg2) &*&
             [?f3]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_cs, ?hmac_key_cg) &*&
               enc_key_cg1 == cg_symmetric_key(sender, ?enc_id1) &*&
               enc_key_cg2 == cg_symmetric_key(sender, ?enc_id2) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               cg_info(enc_key_cg1) == hmac_id &*&
               cg_info(enc_key_cg2) == hmac_id &*&
               shared_with(sender, enc_id1) == shared_with(sender, hmac_id) &*&
               shared_with(sender, enc_id2) == shared_with(sender, hmac_id) &*&
             [?f4]crypto_chars(secret, msg, msg_len, ?msg_cs) &*&
               MAX_SIZE >= msg_len &*& msg_len >= MINIMAL_STRING_SIZE &*&
               bad(sender) || bad(shared_with(sender, enc_id1)) ?
                 [_]public_generated(hmac_then_enc_nested_pub)(msg_cs)
               :
                 // Not saying anything about publicness of msg_cs established
                 // confidentiality
                 true == send(sender, shared_with(sender, enc_id1), msg_cs); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(enc_key1, KEY_SIZE, enc_key_cs1, enc_key_cg1) &*&
             [f2]cryptogram(enc_key2, KEY_SIZE, enc_key_cs2, enc_key_cg2) &*&
             [f3]cryptogram(hmac_key, KEY_SIZE, hmac_key_cs, hmac_key_cg) &*&
             [f4]crypto_chars(secret, msg, msg_len, msg_cs); @*/

int receiver(char *enc_key1, char *enc_key2, char *hmac_key, char *msg);
/*@ requires [_]public_invar(hmac_then_enc_nested_pub) &*&
             [_]decryption_key_classifier(hmac_then_enc_nested_public_key) &*&
             principal(?receiver, _) &*&
             [?f1]cryptogram(enc_key1, KEY_SIZE, ?enc_key_cs1, ?enc_key_cg1) &*&
             [?f2]cryptogram(enc_key2, KEY_SIZE, ?enc_key_cs2, ?enc_key_cg2) &*&
             [?f3]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_cs, ?hmac_key_cg) &*&
               enc_key_cg1 == cg_symmetric_key(?sender, ?enc_id1) &*&
               enc_key_cg2 == cg_symmetric_key(sender, ?enc_id2) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               cg_info(enc_key_cg1) == hmac_id &*&
               cg_info(enc_key_cg2) == hmac_id &*&
               receiver == shared_with(sender, enc_id1) &*&
               receiver == shared_with(sender, enc_id2) &*&
               receiver == shared_with(sender, hmac_id) &*&
             chars(msg, MAX_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(enc_key1, KEY_SIZE, enc_key_cs1, enc_key_cg1) &*&
             [f2]cryptogram(enc_key2, KEY_SIZE, enc_key_cs2, enc_key_cg2) &*&
             [f3]cryptogram(hmac_key, KEY_SIZE, hmac_key_cs, hmac_key_cg) &*&
             chars(msg + result, MAX_SIZE - result, _) &*&
             crypto_chars(secret, msg, result, ?msg_cs) &*&
             col || bad(sender) || bad(receiver) || 
               send(sender, receiver, msg_cs); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PUBLIC_INVARIANT_PROOFS(hmac_then_enc_nested)
//@ DECRYPTION_PROOFS(hmac_then_enc_nested)

#endif
