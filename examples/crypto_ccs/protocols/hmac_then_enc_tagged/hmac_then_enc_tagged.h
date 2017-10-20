#ifndef HMAC_THEN_ENC_TAGGED_H
#define HMAC_THEN_ENC_TAGGED_H

#include "../../annotated_api/mbedTLS_definitions.h"

#define MAX_SIZE 1024
#define KEY_SIZE 32

/*@

// 1. sender -> receiver : ENC(K1, {M, HMAC(K2, M)})

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint int shared_with(int sender, int id);
fixpoint bool send(int sender, int receiver, list<crypto_char> message);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate hmac_then_enc_tagged_proof_pred() = true;

predicate hmac_then_enc_tagged_pub_1(list<crypto_char> cs, cryptogram cg) = true;

fixpoint bool hmac_then_enc_tagged_public_key(int p, int c, bool symmetric)
{
  return symmetric ?
           bad(p) || bad(shared_with(p, c))
         :
           bad(p);
}

predicate hmac_then_enc_tagged_pub(cryptogram cg) =
  switch (cg)
  {
    case cg_nonce(p0, c0):
      return true;
    case cg_symmetric_key(p0, c0):
      return true == hmac_then_enc_tagged_public_key(p0, c0, true);
    case cg_rsa_public_key(p0, c0):
      return true;
    case cg_rsa_private_key(p0, c0):
      return true == hmac_then_enc_tagged_public_key(p0, c0, false);
    case cg_sha512_hash(ccs0):
      return true;
    case cg_sha512_hmac(p0, c0, ccs0):
      return hmac_then_enc_tagged_public_key(p0, c0, true) ?
        true
      :
        [_]memcmp_region(_, ccs0) &*&
        true == send(p0, shared_with(p0, c0), ccs0);
    case cg_aes_encrypted(p0, c0, ccs0, ent0):
      return hmac_then_enc_tagged_public_key(p0, c0, true) ?
        [_]public_ccs(ccs0)
      :
        hmac_then_enc_tagged_pub_1(?msg_ccs, ?hmac_cg) &*&
        ccs0 == append(cs_to_ccs(identifier(0)), 
                       append(msg_ccs, ccs_for_cg(hmac_cg))) &*&
        [_]public_ccs(cs_to_ccs(identifier(0))) &*&
        length(cs_to_ccs(identifier(0))) == ID_SIZE &*&
        length(ccs_for_cg(hmac_cg)) == 64 && cg_is_gen_or_pub(hmac_cg) &*&
        [_]hmac_then_enc_tagged_pub(hmac_cg) &*&
        hmac_cg == cg_sha512_hmac(p0, ?c1, msg_ccs) &*&
        cg_info(cg_symmetric_key(p0, c0)) == c1 &*&
        shared_with(p0, c0) == shared_with(p0, c1) &*&
        [_]memcmp_region(_, msg_ccs) &*&
        true == send(p0, shared_with(p0, c0), msg_ccs);
    case cg_aes_auth_encrypted(p0, c0, ccs0, ent0):
      return true == hmac_then_enc_tagged_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_rsa_encrypted(p0, c0, ccs0, ent0):
      return [_]public_ccs(ccs0);
    case cg_rsa_signature(p0, c0, ccs0, ent0):
      return true == hmac_then_enc_tagged_public_key(p0, c0, false);
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void sender(char *enc_key, char *hmac_key, char *msg, unsigned int msg_len);
/*@ requires [_]public_invar(hmac_then_enc_tagged_pub) &*&
             principal(?sender, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_ccs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               cg_info(enc_key_cg) == hmac_id &*&
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
/*@ requires [_]public_invar(hmac_then_enc_tagged_pub) &*&
             [_]decryption_key_classifier(hmac_then_enc_tagged_public_key) &*&
             principal(?receiver, _) &*&
             [?f1]cryptogram(enc_key, KEY_SIZE, ?enc_key_ccs, ?enc_key_cg) &*&
             [?f2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
               enc_key_cg == cg_symmetric_key(?sender, ?enc_id) &*&
               hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
               cg_info(enc_key_cg) == hmac_id &*&
               receiver == shared_with(sender, enc_id) &*&
               receiver == shared_with(sender, hmac_id) &*&
             chars(msg, MAX_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(enc_key, KEY_SIZE, enc_key_ccs, enc_key_cg) &*&
             [f2]cryptogram(hmac_key, KEY_SIZE, hmac_key_ccs, hmac_key_cg) &*&
             chars(msg + result, MAX_SIZE - result, _) &*&
             crypto_chars(_, msg, result, ?msg_ccs) &*&
             col || bad(sender) || bad(receiver) || 
               send(sender, receiver, msg_ccs); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PUBLIC_INVARIANT_PROOFS(hmac_then_enc_tagged)
//@ DECRYPTION_PROOFS(hmac_then_enc_tagged)

#endif
