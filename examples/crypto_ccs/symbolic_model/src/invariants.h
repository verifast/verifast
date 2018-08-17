#ifndef POLARSSL_INVARIANTS_H
#define POLARSSL_INVARIANTS_H

#include "general.h"

#include "item.h"
#include "nonce_item.h"
#include "key_register.h"
#include "debug.h"

/*@

predicate world(predicate(item) pub, fixpoint(int, int, bool, bool) key_clsfy) =
  nonces_initialized() &*&
  key_registry_initialized(pub) &*&
  [_]public_invar(polarssl_pub(pub)) &*&
  proof_obligations(pub) &*&
  [_]decryption_key_classifier(key_clsfy) &*&
  is_key_classifier(_, pub, key_clsfy)
;

#define POLARSSL_PUB_PAY(ATTACK, NO_ATTACK) \
  [_]exists<bool>(?attack) &*& length(ccs0) <= INT_MAX &*& \
  (attack ? \
     [_]public_ccs(ccs0) &*& ATTACK \
   : \
     [_]item_constraints(?pay0, ccs0, pub) &*& NO_ATTACK \
  )

//Parser does not accept deeper nested macro in this proof
fixpoint int gcm_iv_size() { return GCM_IV_SIZE; }
predicate_ctor polarssl_pub(predicate(item) pub)
                           (cryptogram cg) =
  switch (cg)
  {
    case cg_nonce(p0, c0):
      return [_]pub(nonce_item(p0, c0, 0));
    case cg_symmetric_key(p0, c0):
      return [_]pub(symmetric_key_item(p0, c0));
    case cg_rsa_public_key(p0, c0):
      return [_]pub(public_key_item(p0, c0));
    case cg_rsa_private_key(p0, c0):
      return [_]pub(private_key_item(p0, c0));
    case cg_sha512_hash(ccs0):
      return POLARSSL_PUB_PAY(true, [_]pub(hash_item(some(pay0))));
    case cg_sha512_hmac(p0, c0, ccs0):
      return POLARSSL_PUB_PAY(
               [_]pub(symmetric_key_item(p0, c0)),
               [_]pub(hmac_item(p0, c0, some(pay0))));
    case cg_aes_encrypted(p0, c0, ccs0, iv0):
      return [_]public_ccs(ccs0);
    case cg_aes_auth_encrypted(p0, c0, ccs0, iv0):
      return POLARSSL_PUB_PAY(
               [_]pub(symmetric_key_item(p0, c0)),
               [_]exists<list<crypto_char> >(?ent1) &*&
               [_]pub(symmetric_encrypted_item(p0, c0, some(pay0), ent1)) &*&
               drop(gcm_iv_size, ent1) == iv0
             );
    case cg_rsa_encrypted(p0, c0, ccs0, ent0):
      return POLARSSL_PUB_PAY(
               [_]pub(public_key_item(p0, c0)),
               [_]pub(asymmetric_encrypted_item(p0, c0, some(pay0), ent0)));
    case cg_rsa_signature(p0, c0, ccs0, ent0):
      return POLARSSL_PUB_PAY(
               [_]pub(private_key_item(p0, c0)),
               [_]pub(asymmetric_signature_item(p0, c0, some(pay0), ent0)));
  }
;

predicate_ctor polarssl_proof_pred(predicate(item) pub,
                                   fixpoint(int, int, bool, bool) classifier)() =
  [_]public_invar(polarssl_pub(pub)) &*&
  proof_obligations(pub) &*& is_key_classifier(_, pub, classifier)
;

lemma void retreive_public_invariant_constraints(fixpoint(int, int, bool, bool) clsfy);
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           public_invariant_constraints(polarssl_pub(pub),
                                        polarssl_proof_pred(pub, clsfy));

@*/

#endif
