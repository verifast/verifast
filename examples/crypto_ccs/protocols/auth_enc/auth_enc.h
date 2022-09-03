#ifndef AUTH_ENC_H
#define AUTH_ENC_H

#include "../../annotated_api/mbedTLS_definitions.h"

#define MAX_SIZE 1024
#define KEY_SIZE 32

/*@

// 1. sender -> receiver : AUTH_ENC(K, M)

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint int shared_with(int sender, int id);
fixpoint bool send(int sender, int receiver, list<crypto_char> message);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate auth_enc_proof_pred() = true;

predicate auth_enc_pub_1(int p, list<crypto_char> ccs1, 
                                list<crypto_char> ccs2) = true;

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
    case cg_rsa_public_key(p0, c0):
      return true;
    case cg_rsa_private_key(p0, c0):
      return true == auth_enc_public_key(p0, c0, false);
    case cg_sha512_hash(ccs0):
      return true;
    case cg_sha512_hmac(p0, c0, ccs0):
      return true;
    case cg_aes_encrypted(p0, c0, ccs0, ent0):
      return true == auth_enc_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_aes_auth_encrypted(p0, c0, ccs0, ent0):
      return auth_enc_public_key(p0, c0, true) ?
               [_]public_ccs(ccs0)
             :
               true == send(p0, shared_with(p0, c0), ccs0);
    case cg_rsa_encrypted(p0, c0, ccs0, ent0):
      return [_]public_ccs(ccs0);
    case cg_rsa_signature(p0, c0, ccs0, ent0):
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
             [?f1]cryptogram(key, KEY_SIZE, ?key_ccs, ?key_cg) &*&
               key_cg == cg_symmetric_key(sender, ?id) &*&
             [?f2]crypto_chars(secret, msg, msg_len, ?msg_ccs) &*&
               MAX_SIZE >= msg_len &*& msg_len >= MINIMAL_STRING_SIZE &*&
               bad(sender) || bad(shared_with(sender, id)) ?
                 [_]public_ccs(msg_ccs)
               :
                 true == send(sender, shared_with(sender, id), msg_ccs); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_ccs, key_cg) &*&
             [f2]crypto_chars(secret, msg, msg_len, msg_ccs); @*/

int receiver(char *key, char *msg);
/*@ requires [_]public_invar(auth_enc_pub) &*&
             principal(?receiver, _) &*&
             [?f1]cryptogram(key, KEY_SIZE, ?key_ccs, ?key_cg) &*&
               key_cg == cg_symmetric_key(?sender, ?id) &*&
               receiver == shared_with(sender, id) &*&
             chars_(msg, MAX_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(key, KEY_SIZE, key_ccs, key_cg) &*&
             chars_(msg + result, MAX_SIZE - result, _) &*&
             crypto_chars(secret, msg, result, ?msg_ccs) &*&
             col || bad(sender) || bad(receiver) ||
               send(sender, receiver, msg_ccs); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PUBLIC_INVARIANT_PROOFS(auth_enc)
//@ DECRYPTION_PROOFS(auth_enc)

#endif
