#ifndef AUTH_ENC_H
#define AUTH_ENC_H

#include "../../annotated_api/polarssl_definitions/polarssl_definitions.h"

#define MAX_SIZE 1024
#define KEY_SIZE 32

/*@

// 1. sender -> receiver : AUTH_ENC(K, M)

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint int shared_with(int sender, int id);
fixpoint bool send(int sender, int receiver, list<char> message);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate auth_enc_proof_pred() = true;

predicate auth_enc_pub_1(int p, list<char> cs1, list<char> cs2) = true;

fixpoint bool auth_enc_public_key(int p, int c, bool symmetric)
{
  return symmetric ?
           bad(p) || bad(shared_with(p, c))
         :
           bad(p);
}

predicate auth_enc_pub(cryptogram cg) =
  switch (cg)
  {
    case cg_nonce(p0, c0):
      return true;
    case cg_symmetric_key(p0, c0):
      return true == auth_enc_public_key(p0, c0, true);
    case cg_public_key(p0, c0):
      return true;
    case cg_private_key(p0, c0):
      return true == auth_enc_public_key(p0, c0, false);
    case cg_hash(cs0):
      return true;
    case cg_hmac(p0, c0, cs0):
      return true;
    case cg_encrypted(p0, c0, cs0, ent0):
      return true == auth_enc_public_key(p0, c0, true) &*&
             [_]public_generated(auth_enc_pub)(cs0);
    case cg_auth_encrypted(p0, c0, cs0, ent0):
      return auth_enc_public_key(p0, c0, true) ?
               [_]public_generated(auth_enc_pub)(cs0)
             :
               true == send(p0, shared_with(p0, c0), cs0);
    case cg_asym_encrypted(p0, c0, cs0, ent0):
      return [_]public_generated(auth_enc_pub)(cs0);
    case cg_asym_signature(p0, c0, cs0, ent0):
      return true == auth_enc_public_key(p0, c0, false);
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void sender(char *key, char *msg, unsigned int msg_len);
/*@ requires [_]public_invar(auth_enc_pub) &*&
             principal(?sender, _) &*&
             [?f1]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
               key_cg == cg_symmetric_key(sender, ?id) &*&
             [?f2]crypto_chars(secret, msg, msg_len, ?msg_cs) &*&
               MAX_SIZE >= msg_len &*& msg_len >= MINIMAL_STRING_SIZE &*&
               bad(sender) || bad(shared_with(sender, id)) ?
                 [_]public_generated(auth_enc_pub)(msg_cs)
               :
                 true == send(sender, shared_with(sender, id), msg_cs); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_cs, key_cg) &*&
             [f2]crypto_chars(secret, msg, msg_len, msg_cs); @*/

int receiver(char *key, char *msg);
/*@ requires [_]public_invar(auth_enc_pub) &*&
             principal(?receiver, _) &*&
             [?f1]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
               key_cg == cg_symmetric_key(?sender, ?id) &*&
               receiver == shared_with(sender, id) &*&
             chars(msg, MAX_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_cs, key_cg) &*&
             chars(msg + result, MAX_SIZE - result, _) &*&
             crypto_chars(secret, msg, result, ?msg_cs) &*&
             col || bad(sender) || bad(receiver) ||
               send(sender, receiver, msg_cs); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PUBLIC_INVARIANT_PROOFS(auth_enc)
//@ DECRYPTION_PROOFS(auth_enc)

#endif
