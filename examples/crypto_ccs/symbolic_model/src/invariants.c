#include "invariants.h"

#include "serialization.h"

/*@

lemma void retreive_bad_nonce_is_public(fixpoint(int, int, bool, bool) clsfy)
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_bad_nonce_is_public(_, polarssl_pub(pub),
                                     polarssl_proof_pred(pub, clsfy));
{
  {
    lemma void crypto_bad_nonce_is_public(cryptogram nonce)
      requires  polarssl_proof_pred(pub, clsfy)() &*&
                nonce == cg_nonce(?p__, ?c__) &*&
                true == bad(p__);
      ensures   polarssl_proof_pred(pub, clsfy)() &*&
                [_]polarssl_pub(pub)(nonce);
    {
      open polarssl_proof_pred(pub, clsfy)();
      open proof_obligations(pub);
      assert is_public_nonce(?proof, pub);
      proof(nonce_item(p__, c__, 0));
      close proof_obligations(pub);
      close polarssl_proof_pred(pub, clsfy)();
      close polarssl_pub(pub)(nonce);
      leak polarssl_pub(pub)(nonce);
    }
    produce_lemma_function_pointer_chunk(crypto_bad_nonce_is_public) :
      bad_nonce_is_public
        (polarssl_pub(pub), polarssl_proof_pred(pub, clsfy))(nonce__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(bad_nonce_is_public);};
  }
}

lemma void retreive_bad_key_is_public(fixpoint(int, int, bool, bool) clsfy)
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_bad_key_is_public(_, polarssl_pub(pub),
                                   polarssl_proof_pred(pub, clsfy));
{
  {
    lemma void crypto_bad_key_is_public(cryptogram key)
      requires  polarssl_proof_pred(pub, clsfy)() &*&
                key == cg_symmetric_key(?p__, ?c__) &*&
                true == bad(p__);
      ensures   polarssl_proof_pred(pub, clsfy)() &*&
                [_]polarssl_pub(pub)(key);
    {
      open polarssl_proof_pred(pub, clsfy)();
      open proof_obligations(pub);
      assert is_public_symmetric_key(?proof, pub);
      proof(symmetric_key_item(p__, c__));
      close proof_obligations(pub);
      close polarssl_proof_pred(pub, clsfy)();
      close polarssl_pub(pub)(key);
      leak polarssl_pub(pub)(key);
    }
    produce_lemma_function_pointer_chunk(crypto_bad_key_is_public) :
      bad_key_is_public(polarssl_pub(pub), polarssl_proof_pred(pub, clsfy))(key__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(bad_key_is_public);};
  }
}

lemma void retreive_public_key_is_public(fixpoint(int, int, bool, bool) clsfy)
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_key_is_public(_, polarssl_pub(pub),
                                      polarssl_proof_pred(pub, clsfy));
{
  {
    lemma void crypto_public_key_is_public(cryptogram key)
      requires  polarssl_proof_pred(pub, clsfy)() &*&
                key == cg_rsa_public_key(?p__, ?c__);
      ensures   polarssl_proof_pred(pub, clsfy)() &*&
                [_]polarssl_pub(pub)(key);
    {
      open polarssl_proof_pred(pub, clsfy)();
      open proof_obligations(pub);
      assert is_public_public_key(?proof, pub);
      proof(public_key_item(p__, c__));
      close proof_obligations(pub);
      close polarssl_proof_pred(pub, clsfy)();
      close polarssl_pub(pub)(key);
      leak polarssl_pub(pub)(key);
    }
    produce_lemma_function_pointer_chunk(crypto_public_key_is_public) :
      public_key_is_public(polarssl_pub(pub), polarssl_proof_pred(pub, clsfy))(key__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_key_is_public);};
  }
}

lemma void retreive_bad_private_key_is_public(fixpoint(int, int, bool, bool) clsfy)
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_bad_private_key_is_public(_, polarssl_pub(pub),
                                           polarssl_proof_pred(pub, clsfy));
{
  {
    lemma void crypto_bad_private_key_is_public(cryptogram key)
      requires  polarssl_proof_pred(pub, clsfy)() &*&
                key == cg_rsa_private_key(?p__, ?c__) &*&
                true == bad(p__);
      ensures   polarssl_proof_pred(pub, clsfy)() &*&
                [_]polarssl_pub(pub)(key);
    {
      open polarssl_proof_pred(pub, clsfy)();
      open proof_obligations(pub);
      assert is_public_private_key(?proof, pub);
      proof(private_key_item(p__, c__));
      close proof_obligations(pub);
      close polarssl_proof_pred(pub, clsfy)();
      close polarssl_pub(pub)(key);
      leak polarssl_pub(pub)(key);
    }
    produce_lemma_function_pointer_chunk(
      crypto_bad_private_key_is_public) :
      bad_private_key_is_public
        (polarssl_pub(pub), polarssl_proof_pred(pub, clsfy))(key__) { call(); }
    {duplicate_lemma_function_pointer_chunk(bad_private_key_is_public);};
  }
}

lemma void retreive_hash_is_public(fixpoint(int, int, bool, bool) clsfy)
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_hash_is_public(_, polarssl_pub(pub),
                                polarssl_proof_pred(pub, clsfy));
{
  {
    lemma void crypto_hash_is_public(cryptogram hash)
      requires  polarssl_proof_pred(pub, clsfy)() &*&
                hash == cg_sha512_hash(?pay) &*&
                length(pay) <= INT_MAX &*&
                [_]public_ccs(pay);
      ensures   polarssl_proof_pred(pub, clsfy)() &*&
                [_]polarssl_pub(pub)(hash);
    {
      close exists<bool>(true);
      leak exists<bool>(true);
      close polarssl_pub(pub)(hash);
      leak polarssl_pub(pub)(hash);
    }
    produce_lemma_function_pointer_chunk(crypto_hash_is_public) :
      hash_is_public(polarssl_pub(pub), polarssl_proof_pred(pub, clsfy))(hash)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(hash_is_public);};
  }
}

lemma void retreive_public_hmac_is_public(fixpoint(int, int, bool, bool) clsfy)
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_hmac_is_public(_, polarssl_pub(pub),
                                       polarssl_proof_pred(pub, clsfy));
{
  {
    lemma void crypto_public_hmac_is_public(cryptogram hmac)
      requires  polarssl_proof_pred(pub, clsfy)() &*&
                hmac == cg_sha512_hmac(?p, ?c, ?pay) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(cg_symmetric_key(p, c)) &*&
                [_]public_ccs(pay);
      ensures   polarssl_proof_pred(pub, clsfy)() &*&
                [_]polarssl_pub(pub)(hmac);
    {
      close exists<bool>(true);
      leak exists<bool>(true);
      open [_]polarssl_pub(pub)(cg_symmetric_key(p, c));
      close polarssl_pub(pub)(hmac);
      leak polarssl_pub(pub)(hmac);
    }
    produce_lemma_function_pointer_chunk
      (crypto_public_hmac_is_public) : public_hmac_is_public
        (polarssl_pub(pub), polarssl_proof_pred(pub, clsfy))(hmac) { call(); }
    {duplicate_lemma_function_pointer_chunk(public_hmac_is_public);};
  }
}

lemma void retreive_public_encryption_is_public(fixpoint(int, int, bool, bool) clsfy)
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_encryption_is_public(_, polarssl_pub(pub),
                                             polarssl_proof_pred(pub, clsfy));
{
  {
    lemma void crypto_public_encryption_is_public(cryptogram encrypted)
      requires  polarssl_proof_pred(pub, clsfy)() &*&
                encrypted == cg_aes_encrypted(?p, ?c, ?pay, ?ent) &*&
                [_]polarssl_pub(pub)(cg_symmetric_key(p, c)) &*&
                [_]public_ccs(pay);
      ensures   polarssl_proof_pred(pub, clsfy)() &*&
                [_]polarssl_pub(pub)(encrypted);
    {
      open [_]polarssl_pub(pub)(cg_symmetric_key(p, c));
      close polarssl_pub(pub)(encrypted);
      leak polarssl_pub(pub)(encrypted);
    }
    produce_lemma_function_pointer_chunk
      (crypto_public_encryption_is_public) : public_encryption_is_public
        (polarssl_pub(pub), polarssl_proof_pred(pub, clsfy))(encrypted__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_encryption_is_public);};
  }
}

lemma void retreive_public_decryption_is_public(fixpoint(int, int, bool, bool) clsfy)
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_decryption_is_public(_, polarssl_pub(pub),
                                             polarssl_proof_pred(pub, clsfy));
{
  {
    lemma void crypto_public_decryption_is_public(cryptogram key,
                                                  cryptogram encrypted)
      requires  polarssl_proof_pred(pub, clsfy)() &*&
                key == cg_symmetric_key(?p, ?c) &*&
                encrypted == cg_aes_encrypted(p, c, ?pay, ?ent) &*&
                [_]polarssl_pub(pub)(key) &*&
                [_]polarssl_pub(pub)(encrypted);
      ensures   polarssl_proof_pred(pub, clsfy)() &*&
                [_]public_ccs(pay);
    {
      open [_]polarssl_pub(pub)(key);
      open [_]polarssl_pub(pub)(encrypted);
    }
    produce_lemma_function_pointer_chunk
      (crypto_public_decryption_is_public) : public_decryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub, clsfy))(key__, encrypted__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_decryption_is_public);};
  }
}

lemma void retreive_public_auth_encryption_is_public(fixpoint(int, int, bool, bool) clsfy)
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_auth_encryption_is_public(_,
                                     polarssl_pub(pub), polarssl_proof_pred(pub, clsfy));
{
  {
    lemma void crypto_public_auth_encryption_is_public(
                                              cryptogram encrypted)
      requires  polarssl_proof_pred(pub, clsfy)() &*&
                encrypted == cg_aes_auth_encrypted(?p, ?c, ?pay, ?ent) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(cg_symmetric_key(p, c)) &*&
                [_]public_ccs(pay);
      ensures   polarssl_proof_pred(pub, clsfy)() &*&
                [_]polarssl_pub(pub)(encrypted);
    {
      open [_]polarssl_pub(pub)(cg_symmetric_key(p, c));
      close exists<bool>(true);
      leak exists<bool>(true);
      close polarssl_pub(pub)(encrypted);
      leak polarssl_pub(pub)(encrypted);
    }
    produce_lemma_function_pointer_chunk
      (crypto_public_auth_encryption_is_public) :
        public_auth_encryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub, clsfy))(encrypted__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_auth_encryption_is_public);};
  }
}

lemma void retreive_public_auth_decryption_is_public(fixpoint(int, int, bool, bool) clsfy)
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_auth_decryption_is_public(_, polarssl_pub(pub),
                                                  polarssl_proof_pred(pub, clsfy));
{
  {
    lemma void crypto_public_auth_decryption_is_public(cryptogram key,
                                                       cryptogram encrypted)
      requires  polarssl_proof_pred(pub, clsfy)() &*&
                key == cg_symmetric_key(?p, ?c) &*&
                encrypted == cg_aes_auth_encrypted(p, c, ?pay, ?iv) &*&
                [_]polarssl_pub(pub)(key) &*&
                [_]polarssl_pub(pub)(encrypted);
      ensures   polarssl_proof_pred(pub, clsfy)() &*&
                [_]public_ccs(pay);
    {
      open [_]polarssl_pub(pub)(key);
      open [_]polarssl_pub(pub)(encrypted);
      assert [_]exists<bool>(?b);
      if (b)
      {
        assert [_]public_ccs(pay);
      }
      else
      {
        assert [_]exists<list<crypto_char> >(?ent0);
        assert [_]polarssl_pub(pub)(key);
        assert [_]item_constraints(?pay0, pay, pub);
        item enc = symmetric_encrypted_item(p, c, some(pay0), ent0);
        assert [_]pub(enc);
        assert drop(GCM_IV_SIZE, ent0) == iv;

        open polarssl_proof_pred(pub, clsfy)();
        open proof_obligations(pub);
        assert is_public_symmetric_decrypted(?proof, pub);
        proof(enc);
        close proof_obligations(pub);
        assert [_]pub(pay0);
        serialize_item(pay0);
        close polarssl_proof_pred(pub, clsfy)();
      }
    }
    produce_lemma_function_pointer_chunk
      (crypto_public_auth_decryption_is_public) :
        public_auth_decryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub, clsfy))(key__, encrypted__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_auth_decryption_is_public);};
  }
}

lemma void retreive_public_asym_encryption_is_public(fixpoint(int, int, bool, bool) clsfy)
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_asym_encryption_is_public(_, polarssl_pub(pub),
                                                  polarssl_proof_pred(pub, clsfy));
{
  {
    lemma void crypto_public_asym_encryption_is_public(cryptogram encrypted)
      requires  polarssl_proof_pred(pub, clsfy)() &*&
                encrypted == cg_rsa_encrypted(?p, ?c, ?pay, ?ent) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(cg_rsa_public_key(p, c)) &*&
                [_]public_ccs(pay);
      ensures   polarssl_proof_pred(pub, clsfy)() &*&
                [_]polarssl_pub(pub)(encrypted);
    {
      open [_]polarssl_pub(pub)(cg_rsa_public_key(p, c));
      close exists<bool>(true);
      leak exists<bool>(true);
      close polarssl_pub(pub)(encrypted);
      leak polarssl_pub(pub)(encrypted);
    }
    produce_lemma_function_pointer_chunk
      (crypto_public_asym_encryption_is_public) :
        public_asym_encryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub, clsfy))(encrypted__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_asym_encryption_is_public);};
  }
}

lemma void retreive_public_asym_decryption_is_public(fixpoint(int, int, bool, bool) clsfy)
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_asym_decryption_is_public(_, polarssl_pub(pub),
                                                  polarssl_proof_pred(pub, clsfy));
{
  {
    lemma void crypto_public_asym_decryption_is_public(cryptogram key,
                                                       cryptogram encrypted)
      requires  polarssl_proof_pred(pub, clsfy)() &*&
                key == cg_rsa_private_key(?p, ?c) &*&
                encrypted == cg_rsa_encrypted(p, c, ?pay, ?ent) &*&
                [_]polarssl_pub(pub)(key) &*&
                [_]polarssl_pub(pub)(encrypted);
      ensures   polarssl_proof_pred(pub, clsfy)() &*&
                [_]public_ccs(pay);
    {
      open [_]polarssl_pub(pub)(key);
      open [_]polarssl_pub(pub)(encrypted);
      assert [_]exists<bool>(?b);
      if (b)
      {
        assert [_]public_ccs(pay);
      }
      else
      {
        assert [_]polarssl_pub(pub)(key);
        assert [_]item_constraints(?pay0, pay, pub);
        item enc = asymmetric_encrypted_item(p, c, some(pay0), ent);
        assert [_]pub(enc);

        open polarssl_proof_pred(pub, clsfy)();
        open proof_obligations(pub);
        assert is_public_asymmetric_decrypted(?proof, pub);
        proof(enc);
        close proof_obligations(pub);
        assert [_]pub(pay0);
        serialize_item(pay0);
        close polarssl_proof_pred(pub, clsfy)();
      }
    }
    produce_lemma_function_pointer_chunk
      (crypto_public_asym_decryption_is_public) :
        public_asym_decryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub, clsfy))(key__, encrypted__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_asym_decryption_is_public);};
  }
}

lemma void retreive_public_asym_signature_is_public(fixpoint(int, int, bool, bool) clsfy)
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_asym_signature_is_public(_, polarssl_pub(pub),
                                                 polarssl_proof_pred(pub, clsfy));
{
  {
    lemma void crypto_public_asym_signature_is_public(cryptogram sig)
      requires  polarssl_proof_pred(pub, clsfy)() &*&
                sig == cg_rsa_signature(?p, ?c, ?pay, ?ent) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(cg_rsa_private_key(p, c)) &*&
                [_]public_ccs(pay);
      ensures   polarssl_proof_pred(pub, clsfy)() &*&
                [_]polarssl_pub(pub)(sig);
    {
      open [_]polarssl_pub(pub)(cg_rsa_private_key(p, c));
      close exists<bool>(true);
      leak exists<bool>(true);
      close polarssl_pub(pub)(sig);
      leak polarssl_pub(pub)(sig);
    }
    produce_lemma_function_pointer_chunk
      (crypto_public_asym_signature_is_public) :
        public_asym_signature_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub, clsfy))(sig__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_asym_signature_is_public);};
  }
}

lemma void retreive_public_invariant_constraints(fixpoint(int, int, bool, bool) clsfy)
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           public_invariant_constraints(polarssl_pub(pub),
                                        polarssl_proof_pred(pub, clsfy));
{
  retreive_bad_nonce_is_public(clsfy);
  retreive_bad_key_is_public(clsfy);
  retreive_public_key_is_public(clsfy);
  retreive_bad_private_key_is_public(clsfy);
  retreive_hash_is_public(clsfy);
  retreive_public_hmac_is_public(clsfy);
  retreive_public_encryption_is_public(clsfy);
  retreive_public_decryption_is_public(clsfy);
  retreive_public_auth_encryption_is_public(clsfy);
  retreive_public_auth_decryption_is_public(clsfy);
  retreive_public_asym_encryption_is_public(clsfy);
  retreive_public_asym_decryption_is_public(clsfy);
  retreive_public_asym_signature_is_public(clsfy);

  close public_invariant_constraints(polarssl_pub(pub),
                                     polarssl_proof_pred(pub, clsfy));
}

@*/
