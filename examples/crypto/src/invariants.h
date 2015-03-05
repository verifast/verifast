#ifndef POLARSSL_INVARIANTS_H
#define POLARSSL_INVARIANTS_H

#include "general.h"

#include "item.h"
#include "nonce_item.h"
#include "key_register.h"
#include "debug.h"

/*@

predicate world(predicate(item) pub) =
  nonces_initialized() &*&
  key_registry_initialized(pub) &*&
  polarssl_world(polarssl_pub(pub)) &*&
  proof_obligations(pub)
;

predicate info_for_item(item i, int info) =
  info == polarssl_info_for_item(i)
;

predicate_ctor polarssl_pub(predicate(item) pub)
                           (polarssl_cryptogram cg) =
  switch (cg)
  {
    case polarssl_random(p0, c0):
      return [_]pub(nonce_item(p0, c0, 0));
    case polarssl_symmetric_key(p0, c0):
      return [_]pub(symmetric_key_item(p0, c0));
    case polarssl_public_key(p0, c0):
      return [_]pub(public_key_item(p0, c0));
    case polarssl_private_key(p0, c0):
      return [_]pub(private_key_item(p0, c0));
    case polarssl_hash(cs0):
      return length(cs0) <= INT_MAX &*&
             [_]exists<bool>(?collision) &*& collision ?
             (
               true == subset(polarssl_cryptograms_in_chars(cs0),
                 polarssl_generated_public_cryptograms(polarssl_pub(pub)))
             )
             :
             (
               [_]item_constraints_no_collision(?pay0, cs0, pub) &*&
               [_]pub(hash_item(some(pay0)))
             );
    case polarssl_hmac(p0, c0, cs0):
      return length(cs0) <= INT_MAX &*&
             [_]exists<bool>(?collision) &*& collision ?
             (
               [_]pub(symmetric_key_item(p0, c0)) &*&
               true == subset(polarssl_cryptograms_in_chars(cs0),
                 polarssl_generated_public_cryptograms(polarssl_pub(pub)))
             )
             :
             (
               [_]item_constraints_no_collision(?pay0, cs0, pub) &*&
               [_]pub(hmac_item(p0, c0, some(pay0)))
             );
    case polarssl_encrypted(p0, c0, cs0, iv0):
      return true == subset(polarssl_cryptograms_in_chars(cs0),
               polarssl_generated_public_cryptograms(polarssl_pub(pub)));
    case polarssl_auth_encrypted(p0, c0, mac0, cs0, iv0):
      return length(cs0) <= INT_MAX &*&
             [_]exists<bool>(?collision) &*& collision ?
             (
               [_]pub(symmetric_key_item(p0, c0)) &*&
               true == subset(polarssl_cryptograms_in_chars(cs0),
                 polarssl_generated_public_cryptograms(polarssl_pub(pub)))
             )
             :
             (
               [_]item_constraints_no_collision(?pay0, cs0, pub) &*&
               [_]exists<list<char> >(?ent1) &*&
               [_]pub(symmetric_encrypted_item(p0, c0, some(pay0), ent1)) &*&
               drop(GCM_ENT_SIZE, ent1) == cons(length(mac0), append(mac0, iv0))
             );
    case polarssl_asym_encrypted(p0, c0, cs0, ent0):
      return length(cs0) <= INT_MAX &*&
             [_]exists<bool>(?collision) &*& collision ?
             (
               [_]pub(public_key_item(p0, c0)) &*&
               true == subset(polarssl_cryptograms_in_chars(cs0),
                 polarssl_generated_public_cryptograms(polarssl_pub(pub)))
             )
             :
             (
               [_]item_constraints_no_collision(?pay0, cs0, pub) &*&
               [_]pub(asymmetric_encrypted_item(p0, c0, some(pay0), ent0))
             );
    case polarssl_asym_signature(p0, c0, cs0, ent0):
      return length(cs0) <= INT_MAX &*&
             [_]exists<bool>(?collision) &*& collision ?
             (
               [_]pub(private_key_item(p0, c0)) &*&
               true == subset(polarssl_cryptograms_in_chars(cs0),
                 polarssl_generated_public_cryptograms(polarssl_pub(pub)))
             )
             :
             (
               [_]item_constraints_no_collision(?pay0, cs0, pub) &*&
               [_]pub(asymmetric_signature_item(p0, c0, some(pay0), ent0))
             );
  }
;

predicate_ctor polarssl_proof_pred(predicate(item) pub)() =
  proof_obligations(pub)
;
                           
fixpoint int polarssl_info_for_item(item i)
{
  switch(i)
  {
    case data_item(cs0):
      return 0;
    case pair_item(f0, s0):
      return 0;
    case nonce_item(p0, c0, inc0): 
      return polarssl_cryptogram_info(
               polarssl_random(p0, c0));
    case hash_item(pay0): 
      return 0;
    case symmetric_key_item(p0, c0): 
      return polarssl_cryptogram_info(
               polarssl_symmetric_key(p0, c0));
    case public_key_item(p0, c0): 
      return polarssl_cryptogram_info(
               polarssl_public_key(p0, c0));
    case private_key_item(p0, c0): 
      return polarssl_cryptogram_info(
               polarssl_private_key(p0, c0));
    case hmac_item(p0, c0, pay0):
      return 0;
    case symmetric_encrypted_item(p0, c0, pay0, ent0):
      return polarssl_cryptogram_info(
               polarssl_symmetric_key(p0, c0));
    case asymmetric_encrypted_item(p0, c0, pay0, ent0):
      return polarssl_cryptogram_info(
               polarssl_public_key(p0, c0));
    case asymmetric_signature_item(p0, c0, pay0, ent0):
      return polarssl_cryptogram_info(
               polarssl_private_key(p0, c0));
  }
}

lemma void retreive_polarssl_proof_obligations();
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           polarssl_proof_obligations(polarssl_pub(pub), 
                                      polarssl_proof_pred(pub));

@*/ 

#endif
