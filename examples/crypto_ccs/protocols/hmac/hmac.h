#ifndef HMAC_H
#define HMAC_H

#include "../../annotated_api/mbedTLS_definitions.h"

#define MESSAGE_SIZE 40

/*@

// 1. sender -> receiver : {M, HMAC(K, M)}

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint int shared_with(int sender, int id);
fixpoint bool send(int sender, int receiver, list<char> message);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate hmac_proof_pred() = true;

fixpoint bool hmac_public_key(int p, int c, bool symmetric)
{
  return symmetric ?
           bad(p) || bad(shared_with(p, c))
         :
           bad(p);
}

predicate hmac_pub(cryptogram cg) =
  switch (cg)
  {
    case cg_nonce(p0, c0):
      return true;
    case cg_symmetric_key(p0, c0):
      return true == hmac_public_key(p0, c0, true);
    case cg_rsa_public_key(p0, c0):
      return true;
    case cg_rsa_private_key(p0, c0):
      return true == hmac_public_key(p0, c0, false);
    case cg_sha512_hash(ccs0):
      return true;
    case cg_sha512_hmac(p0, c0, ccs0):
      return hmac_public_key(p0, c0, true) ? true :
               exists(?cs0) &*& ccs0 == cs_to_ccs(cs0) &*&
               true == send(p0, shared_with(p0, c0), cs0);
    case cg_aes_encrypted(p0, c0, ccs0, ent0):
      return true == hmac_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_aes_auth_encrypted(p0, c0, ccs0, ent0):
      return true == hmac_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_rsa_encrypted(p0, c0, ccs0, ent0):
      return [_]public_ccs(ccs0);
    case cg_rsa_signature(p0, c0, ccs0, ent0):
      return true == hmac_public_key(p0, c0, false);
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void sender(char *key, int key_len, char *message);
  /*@ requires [_]public_invar(hmac_pub) &*&
               principal(?sender, _) &*&
               [?f1]cryptogram(key, key_len, ?key_ccs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(sender, ?id) &*&
               [?f2]chars(message, MESSAGE_SIZE, ?msg_cs) &*&
               true == send(sender, shared_with(sender, id), msg_cs); @*/
  /*@ ensures  principal(sender, _) &*&
               [f1]cryptogram(key, key_len, key_ccs, key_cg) &*&
               [f2]chars(message, MESSAGE_SIZE, msg_cs); @*/

void receiver(char *key, int key_len, char *message);
  /*@ requires [_]public_invar(hmac_pub) &*&
               principal(?receiver, _) &*&
               [?f1]cryptogram(key, key_len, ?key_ccs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(?sender, ?id) &*&
                 receiver == shared_with(sender, id) &*&
               chars_(message, MESSAGE_SIZE, _); @*/
  /*@ ensures  principal(receiver, _) &*&
               [f1]cryptogram(key, key_len, key_ccs, key_cg) &*&
               chars(message, MESSAGE_SIZE, ?msg_cs) &*&
               col || bad(sender) || bad(receiver) ||
               send(sender, receiver, msg_cs); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PUBLIC_INVARIANT_PROOFS(hmac)
//@ DECRYPTION_PROOFS(hmac)

#endif
