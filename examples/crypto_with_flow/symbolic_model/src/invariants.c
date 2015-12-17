#include "invariants.h"

#include "serialization.h"

/*@

lemma void get_info_for_item(item i)
  requires true;
  ensures  [_]info_for_item(i, ?info);
{
  close info_for_item(i, _);
  leak info_for_item(i, _);
}

lemma void retreive_bad_nonce_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_bad_nonce_is_public(_, polarssl_pub(pub),
                                      polarssl_proof_pred(pub));
{
  {
    lemma void crypto_bad_nonce_is_public(cryptogram nonce)
      requires  polarssl_proof_pred(pub)() &*&
                nonce == cg_nonce(?p__, ?c__) &*&
                true == bad(p__);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(nonce);
    {
      open polarssl_proof_pred(pub)();
      open proof_obligations(pub);
      assert is_public_nonce(?proof, pub);
      proof(nonce_item(p__, c__, 0));
      close proof_obligations(pub);
      close polarssl_proof_pred(pub)();
      close polarssl_pub(pub)(nonce);
      leak polarssl_pub(pub)(nonce);
    }
    produce_lemma_function_pointer_chunk(crypto_bad_nonce_is_public) :
      bad_nonce_is_public
        (polarssl_pub(pub), polarssl_proof_pred(pub))(nonce__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(bad_nonce_is_public);};
  }
}

lemma void retreive_bad_key_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_bad_key_is_public(_, polarssl_pub(pub),
                                   polarssl_proof_pred(pub));
{
  {
    lemma void crypto_bad_key_is_public(cryptogram key)
      requires  polarssl_proof_pred(pub)() &*&
                key == cg_symmetric_key(?p__, ?c__) &*&
                true == bad(p__);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(key);
    {
      open polarssl_proof_pred(pub)();
      open proof_obligations(pub);
      assert is_public_symmetric_key(?proof, pub);
      proof(symmetric_key_item(p__, c__));
      close proof_obligations(pub);
      close polarssl_proof_pred(pub)();
      close polarssl_pub(pub)(key);
      leak polarssl_pub(pub)(key);
    }
    produce_lemma_function_pointer_chunk(crypto_bad_key_is_public) :
      bad_key_is_public(polarssl_pub(pub), polarssl_proof_pred(pub))(key__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(bad_key_is_public);};
  }
}

lemma void retreive_public_key_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_key_is_public(_, polarssl_pub(pub),
                                      polarssl_proof_pred(pub));
{
  {
    lemma void crypto_public_key_is_public(cryptogram key)
      requires  polarssl_proof_pred(pub)() &*&
                key == cg_public_key(?p__, ?c__);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(key);
    {
      open polarssl_proof_pred(pub)();
      open proof_obligations(pub);
      assert is_public_public_key(?proof, pub);
      proof(public_key_item(p__, c__));
      close proof_obligations(pub);
      close polarssl_proof_pred(pub)();
      close polarssl_pub(pub)(key);
      leak polarssl_pub(pub)(key);
    }
    produce_lemma_function_pointer_chunk(crypto_public_key_is_public) :
      public_key_is_public(polarssl_pub(pub), polarssl_proof_pred(pub))(key__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_key_is_public);};
  }
}

lemma void retreive_bad_private_key_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_bad_private_key_is_public(_, polarssl_pub(pub),
                                           polarssl_proof_pred(pub));
{
  {
    lemma void crypto_bad_private_key_is_public(cryptogram key)
      requires  polarssl_proof_pred(pub)() &*&
                key == cg_private_key(?p__, ?c__) &*&
                true == bad(p__);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(key);
    {
      open polarssl_proof_pred(pub)();
      open proof_obligations(pub);
      assert is_public_private_key(?proof, pub);
      proof(private_key_item(p__, c__));
      close proof_obligations(pub);
      close polarssl_proof_pred(pub)();
      close polarssl_pub(pub)(key);
      leak polarssl_pub(pub)(key);
    }
    produce_lemma_function_pointer_chunk(
      crypto_bad_private_key_is_public) :
      bad_private_key_is_public
        (polarssl_pub(pub), polarssl_proof_pred(pub))(key__) { call(); }
    {duplicate_lemma_function_pointer_chunk(bad_private_key_is_public);};
  }
}

lemma void retreive_hash_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_hash_is_public(_, polarssl_pub(pub),
                                polarssl_proof_pred(pub));
{
  {
    lemma void crypto_hash_is_public(cryptogram hash)
      requires  polarssl_proof_pred(pub)() &*&
                hash == cg_hash(?pay) &*&
                length(pay) <= INT_MAX &*&
                [_]public_generated(polarssl_pub(pub))(pay);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(hash);
    {
      close exists<bool>(true);
      leak exists<bool>(true);
      close polarssl_pub(pub)(hash);
      leak polarssl_pub(pub)(hash);
    }
    produce_lemma_function_pointer_chunk(crypto_hash_is_public) :
      hash_is_public(polarssl_pub(pub), polarssl_proof_pred(pub))(hash)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(hash_is_public);};
  }
}

lemma void retreive_public_hmac_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_hmac_is_public(_, polarssl_pub(pub),
                                       polarssl_proof_pred(pub));
{
  {
    lemma void crypto_public_hmac_is_public(cryptogram hmac)
      requires  polarssl_proof_pred(pub)() &*&
                hmac == cg_hmac(?p, ?c, ?pay) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(cg_symmetric_key(p, c)) &*&
                [_]public_generated(polarssl_pub(pub))(pay);
      ensures   polarssl_proof_pred(pub)() &*&
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
        (polarssl_pub(pub), polarssl_proof_pred(pub))(hmac) { call(); }
    {duplicate_lemma_function_pointer_chunk(public_hmac_is_public);};
  }
}

lemma void retreive_public_encryption_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_encryption_is_public(_, polarssl_pub(pub),
                                             polarssl_proof_pred(pub));
{
  {
    lemma void crypto_public_encryption_is_public(cryptogram encrypted)
      requires  polarssl_proof_pred(pub)() &*&
                encrypted == cg_encrypted(?p, ?c, ?pay, ?ent) &*&
                [_]polarssl_pub(pub)(cg_symmetric_key(p, c)) &*&
                [_]public_generated(polarssl_pub(pub))(pay);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(encrypted);
    {
      open [_]polarssl_pub(pub)(cg_symmetric_key(p, c));
      close polarssl_pub(pub)(encrypted);
      leak polarssl_pub(pub)(encrypted);
    }
    produce_lemma_function_pointer_chunk
      (crypto_public_encryption_is_public) : public_encryption_is_public
        (polarssl_pub(pub), polarssl_proof_pred(pub))(encrypted__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_encryption_is_public);};
  }
}

lemma void retreive_public_decryption_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_decryption_is_public(_, polarssl_pub(pub),
                                             polarssl_proof_pred(pub));
{
  {
    lemma void crypto_public_decryption_is_public(cryptogram key,
                                                  cryptogram encrypted)
      requires  polarssl_proof_pred(pub)() &*&
                key == cg_symmetric_key(?p, ?c) &*&
                encrypted == cg_encrypted(p, c, ?pay, ?ent) &*&
                [_]polarssl_pub(pub)(key) &*&
                [_]polarssl_pub(pub)(encrypted);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]public_generated(polarssl_pub(pub))(pay);
    {
      open [_]polarssl_pub(pub)(key);
      open [_]polarssl_pub(pub)(encrypted);
    }
    produce_lemma_function_pointer_chunk
      (crypto_public_decryption_is_public) : public_decryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub))(key__, encrypted__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_decryption_is_public);};
  }
}

lemma void retreive_public_auth_encryption_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_auth_encryption_is_public(_,
                                     polarssl_pub(pub), polarssl_proof_pred(pub));
{
  {
    lemma void crypto_public_auth_encryption_is_public(
                                              cryptogram encrypted)
      requires  polarssl_proof_pred(pub)() &*&
                encrypted == cg_auth_encrypted(?p, ?c, ?mac, ?pay, ?ent) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(cg_symmetric_key(p, c)) &*&
                [_]public_generated(polarssl_pub(pub))(pay);
      ensures   polarssl_proof_pred(pub)() &*&
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
          (polarssl_pub(pub), polarssl_proof_pred(pub))(encrypted__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_auth_encryption_is_public);};
  }
}

lemma void retreive_public_auth_decryption_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_auth_decryption_is_public(_, polarssl_pub(pub),
                                                  polarssl_proof_pred(pub));
{
  {
    lemma void crypto_public_auth_decryption_is_public(cryptogram key,
                                                       cryptogram encrypted)
      requires  polarssl_proof_pred(pub)() &*&
                key == cg_symmetric_key(?p, ?c) &*&
                encrypted == cg_auth_encrypted(p, c, ?mac, ?pay, ?iv) &*&
                [_]polarssl_pub(pub)(key) &*&
                [_]polarssl_pub(pub)(encrypted);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]public_generated(polarssl_pub(pub))(pay);
    {
      open [_]polarssl_pub(pub)(key);
      open [_]polarssl_pub(pub)(encrypted);
      assert [_]exists<bool>(?b);
      if (b)
      {
        assert [_]public_generated(polarssl_pub(pub))(pay);
      }
      else
      {
        assert [_]exists<list<char> >(?ent0);
        assert [_]polarssl_pub(pub)(key);
        assert [_]item_constraints(?pay0, pay, pub);
        item enc = symmetric_encrypted_item(p, c, some(pay0), ent0);
        assert [_]pub(enc);
        assert drop(GCM_ENT_SIZE, ent0) == cons(length(mac), append(mac, iv));
        
        open polarssl_proof_pred(pub)();
        open proof_obligations(pub);
        assert is_public_symmetric_decrypted(?proof, pub);
        proof(enc);
        close proof_obligations(pub);
        assert [_]pub(pay0);
        serialize_item(pay0);
        close polarssl_proof_pred(pub)();      
      }
    }
    produce_lemma_function_pointer_chunk
      (crypto_public_auth_decryption_is_public) :
        public_auth_decryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub))(key__, encrypted__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_auth_decryption_is_public);};
  }
}

lemma void retreive_public_asym_encryption_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_asym_encryption_is_public(_, polarssl_pub(pub),
                                                  polarssl_proof_pred(pub));
{
  {
    lemma void crypto_public_asym_encryption_is_public(cryptogram encrypted)
      requires  polarssl_proof_pred(pub)() &*&
                encrypted == cg_asym_encrypted(?p, ?c, ?pay, ?ent) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(cg_public_key(p, c)) &*&
                [_]public_generated(polarssl_pub(pub))(pay);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(encrypted);
    {
      open [_]polarssl_pub(pub)(cg_public_key(p, c));
      close exists<bool>(true);
      leak exists<bool>(true);
      close polarssl_pub(pub)(encrypted);
      leak polarssl_pub(pub)(encrypted);
    }
    produce_lemma_function_pointer_chunk
      (crypto_public_asym_encryption_is_public) :
        public_asym_encryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub))(encrypted__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_asym_encryption_is_public);};
  }
}

lemma void retreive_public_asym_decryption_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_asym_decryption_is_public(_, polarssl_pub(pub),
                                                  polarssl_proof_pred(pub));
{
  {
    lemma void crypto_public_asym_decryption_is_public(cryptogram key,
                                                       cryptogram encrypted)
      requires  polarssl_proof_pred(pub)() &*&
                key == cg_private_key(?p, ?c) &*&
                encrypted == cg_asym_encrypted(p, c, ?pay, ?ent) &*&
                [_]polarssl_pub(pub)(key) &*&
                [_]polarssl_pub(pub)(encrypted);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]public_generated(polarssl_pub(pub))(pay);
    {
      open [_]polarssl_pub(pub)(key);
      open [_]polarssl_pub(pub)(encrypted);
      assert [_]exists<bool>(?b);
      if (b)
      {
        assert [_]public_generated(polarssl_pub(pub))(pay);
      }
      else
      {
        assert [_]polarssl_pub(pub)(key);
        assert [_]item_constraints(?pay0, pay, pub);
        item enc = asymmetric_encrypted_item(p, c, some(pay0), ent);
        assert [_]pub(enc);

        open polarssl_proof_pred(pub)();
        open proof_obligations(pub);
        assert is_public_asymmetric_decrypted(?proof, pub);
        proof(enc);
        close proof_obligations(pub);
        assert [_]pub(pay0);
        serialize_item(pay0);
        close polarssl_proof_pred(pub)();
      }
    }
    produce_lemma_function_pointer_chunk
      (crypto_public_asym_decryption_is_public) :
        public_asym_decryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub))(key__, encrypted__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_asym_decryption_is_public);};
  }
}

lemma void retreive_public_asym_signature_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_public_asym_signature_is_public(_, polarssl_pub(pub),
                                                 polarssl_proof_pred(pub));
{
  {
    lemma void crypto_public_asym_signature_is_public(cryptogram sig)
      requires  polarssl_proof_pred(pub)() &*&
                sig == cg_asym_signature(?p, ?c, ?pay, ?ent) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(cg_private_key(p, c)) &*&
                [_]public_generated(polarssl_pub(pub))(pay);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(sig);
    {
      open [_]polarssl_pub(pub)(cg_private_key(p, c));
      close exists<bool>(true);
      leak exists<bool>(true);
      close polarssl_pub(pub)(sig);
      leak polarssl_pub(pub)(sig);
    }
    produce_lemma_function_pointer_chunk
      (crypto_public_asym_signature_is_public) :
        public_asym_signature_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub))(sig__)
    { call(); }
    {duplicate_lemma_function_pointer_chunk(public_asym_signature_is_public);};
  }
}

lemma void retreive_public_invariant_constraints()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           public_invariant_constraints(polarssl_pub(pub),
                                        polarssl_proof_pred(pub));
{
  retreive_bad_nonce_is_public();
  retreive_bad_key_is_public();
  retreive_public_key_is_public();
  retreive_bad_private_key_is_public();
  retreive_hash_is_public();
  retreive_public_hmac_is_public();
  retreive_public_encryption_is_public();
  retreive_public_decryption_is_public();
  retreive_public_auth_encryption_is_public();
  retreive_public_auth_decryption_is_public();
  retreive_public_asym_encryption_is_public();
  retreive_public_asym_decryption_is_public();
  retreive_public_asym_signature_is_public();

  close public_invariant_constraints(polarssl_pub(pub),
                                     polarssl_proof_pred(pub));
}

@*/
