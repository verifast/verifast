#ifndef ENC_AND_HMAC_H
#define ENC_AND_HMAC_H

#include "../../annotated_api/mbedTLS_definitions.h"

#define MAX_SIZE 1024
#define KEY_SIZE 32

/*@

// 1. sender -> receiver : {ENC(K1, M), HMAC(K2, M)}

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint int shared_with(int sender, int id);
fixpoint bool send(int sender, int receiver, list<crypto_char> message);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate enc_and_hmac_proof_pred() = true;

fixpoint bool enc_and_hmac_public_key(int p, int c, bool symmetric)
{
  return symmetric ?
           bad(p) || bad(shared_with(p, c))
         :
           bad(p);
}

predicate enc_and_hmac_pub(cryptogram cg) =
  switch (cg)
  {
    case cg_nonce(p0, c0):
      return true;
    case cg_symmetric_key(p0, c0):
      return true == enc_and_hmac_public_key(p0, c0, true);
    case cg_rsa_public_key(p0, c0):
      return true;
    case cg_rsa_private_key(p0, c0):
      return true == enc_and_hmac_public_key(p0, c0, false);
    case cg_sha512_hash(ccs0):
      return true;
    case cg_sha512_hmac(p0, c0, ccs0):
      return enc_and_hmac_public_key(p0, c0, true) ?
        [_]public_ccs(ccs0)
      :
        [_]memcmp_region(_, ccs0) &*&
        true == send(p0, shared_with(p0, c0), ccs0);
    case cg_aes_encrypted(p0, c0, ccs0, ent0):
      return enc_and_hmac_public_key(p0, c0, true) ?
        [_]public_ccs(ccs0)
      :
        [_]memcmp_region(_, ccs0) &*&
        true == send(p0, shared_with(p0, c0), ccs0);
    case cg_aes_auth_encrypted(p0, c0, ccs0, ent0):
      return true == enc_and_hmac_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_rsa_encrypted(p0, c0, ccs0, ent0):
      return [_]public_ccs(ccs0);
    case cg_rsa_signature(p0, c0, ccs0, ent0):
      return true == enc_and_hmac_public_key(p0, c0, false);
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void sender(char *enc_key, char *hmac_key, char *msg, unsigned int msg_len);
/*@ requires [_]public_invar(enc_and_hmac_pub) &*&
             principal(?sender, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_ccs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               shared_with(sender, enc_id) == shared_with(sender, hmac_id) &*&
             [?f3]crypto_chars(secret, msg, msg_len, ?msg_ccs) &*&
               MAX_SIZE >= msg_len &*& msg_len >= MINIMAL_STRING_SIZE &*&
               bad(sender) || bad(shared_with(sender, enc_id)) ?
                 [_]public_ccs(msg_ccs)
               :
                 [_]memcmp_region(_, msg_ccs) &*&
                 true == send(sender, shared_with(sender, enc_id), msg_ccs); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(enc_key, KEY_SIZE, enc_key_ccs, enc_key_cg) &*&
             [f2]cryptogram(hmac_key, KEY_SIZE, hmac_key_ccs, hmac_key_cg) &*&
             [f3]crypto_chars(secret, msg, msg_len, msg_ccs); @*/

int receiver(char *enc_key, char *hmac_key, char *msg);
/*@ requires [_]public_invar(enc_and_hmac_pub) &*&
             [_]decryption_key_classifier(enc_and_hmac_public_key) &*&
             principal(?receiver, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_ccs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(?sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               receiver == shared_with(sender, enc_id) &*&
               receiver == shared_with(sender, hmac_id) &*&
             chars_(msg, MAX_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(enc_key, KEY_SIZE, enc_key_ccs, enc_key_cg) &*&
             [f2]cryptogram(hmac_key, KEY_SIZE, hmac_key_ccs, hmac_key_cg) &*&
             chars_(msg + result, MAX_SIZE - result, _) &*&
             crypto_chars(secret, msg, result, ?msg_ccs) &*&
             [_]memcmp_region(_, msg_ccs) &*&
             col || bad(sender) || bad(receiver) ||
               send(sender, receiver, msg_ccs); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PUBLIC_INVARIANT_PROOFS(enc_and_hmac)
//@ DECRYPTION_PROOFS(enc_and_hmac)

#endif
