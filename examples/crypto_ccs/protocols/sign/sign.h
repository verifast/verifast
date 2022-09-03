#ifndef SIGN_H
#define SIGN_H

#include "../../annotated_api/mbedTLS_definitions.h"

#define MSG_SIZE 1024
#define MAX_KEY_SIZE 8192

/*@

// 1. sender -> receiver : {receiver, M, SIGN(K_priv, HASH({receiver, M}))}

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint bool send(int sender, int receiver, list<char> message);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate sign_proof_pred() = true;

predicate sign_pub_1(list<char> message, int receiver) = true;

fixpoint bool sign_public_key(int p, int c, bool symmetric)
{
  return bad(p);
}

predicate sign_pub(cryptogram cg) =
  switch (cg)
  {
    case cg_nonce(p0, c0):
      return true;
    case cg_symmetric_key(p0, c0):
      return true == sign_public_key(p0, c0, true);
    case cg_rsa_public_key(p0, c0):
      return true;
    case cg_rsa_private_key(p0, c0):
      return true == sign_public_key(p0, c0, false);
    case cg_sha512_hash(ccs0):
      return true;
    case cg_sha512_hmac(p0, c0, ccs0):
      return true == sign_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_aes_encrypted(p0, c0, ccs0, ent0):
      return true == sign_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_aes_auth_encrypted(p0, c0, ccs0, ent0):
      return true == sign_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_rsa_encrypted(p0, c0, ccs0, ent0):
      return [_]public_ccs(ccs0);
    case cg_rsa_signature(p0, c0, ccs0, ent0):
      return col || true == sign_public_key(p0, c0, false) ?
               true
             :
               sign_pub_1(?cs1, ?receiver) &*&
               sizeof(int) == length(chars_of_int(receiver)) &&
               ccs0 == ccs_for_cg(cg_sha512_hash(cs_to_ccs(
                         append(chars_of_int(receiver), cs1)))) &&
               send(p0, receiver, cs1);
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void sender(int recvr, char *key, int key_len, char *msg);
  /*@ requires [_]public_invar(sign_pub) &*&
               principal(?sender, _) &*&
               [?f1]cryptogram(key, key_len, ?key_ccs, ?key_cg) &*&
                 key_cg == cg_rsa_private_key(sender, ?id) &*&
                 key_len >= 512 &*& key_len < MAX_KEY_SIZE &*&
               [?f2]chars(msg, MSG_SIZE, ?msg_cs) &*&
               true == send(sender, recvr, msg_cs); @*/
  /*@ ensures  principal(sender, _) &*&
               [f1]cryptogram(key, key_len, key_ccs, key_cg) &*&
               [f2]chars(msg, MSG_SIZE, msg_cs); @*/

void receiver(int recvr, char *key, int key_len, char *msg);
  /*@ requires [_]public_invar(sign_pub) &*&
               principal(recvr, _) &*&
               [?f1]cryptogram(key, key_len, ?key_ccs, ?key_cg) &*&
                 key_cg == cg_rsa_public_key(?sender, ?id) &*&
                 key_len <= MAX_KEY_SIZE &*&
               chars_(msg, MSG_SIZE, _); @*/
  /*@ ensures  principal(recvr, _) &*&
               [f1]cryptogram(key, key_len, key_ccs, key_cg) &*&
               chars(msg, MSG_SIZE, ?msg_cs) &*&
               col || bad(sender) ||
                 send(sender, recvr, msg_cs); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PUBLIC_INVARIANT_PROOFS(sign)
//@ DECRYPTION_PROOFS(sign)

#endif
