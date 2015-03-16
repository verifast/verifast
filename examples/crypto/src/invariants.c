#include "invariants.h"

#include "serialization.h"

/*@

lemma void info_for_item_is_function(item i, int info1, int info2)
  requires [?f1]info_for_item(i, info1) &*& 
           [?f2]info_for_item(i, info2);
  ensures  info1 == info2;
{
  open [f1]info_for_item(i, info1);
  open [f2]info_for_item(i, info2);
}

lemma void get_info_for_item(item i)
  requires true;
  ensures  [_]info_for_item(i, ?info);
{
  close info_for_item(i, polarssl_info_for_item(i));
  leak info_for_item(i, polarssl_info_for_item(i));
}

lemma void retreive_polarssl_bad_random_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_bad_random_is_public(_, polarssl_pub(pub), 
                                               polarssl_proof_pred(pub));
{
  {
    lemma void crypto_polarssl_bad_random_is_public(polarssl_cryptogram random)
      requires  polarssl_proof_pred(pub)() &*&
                random == polarssl_random(?p__, ?c__) &*&
                true == bad(p__);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(random);
    {
      open polarssl_proof_pred(pub)();
      open proof_obligations(pub);
      assert is_public_nonce(?proof, pub);
      proof(nonce_item(p__, c__, 0));
      close proof_obligations(pub);
      close polarssl_proof_pred(pub)();
      close polarssl_pub(pub)(random);
      leak polarssl_pub(pub)(random);
    }
    produce_lemma_function_pointer_chunk(crypto_polarssl_bad_random_is_public) :
      polarssl_bad_random_is_public
        (polarssl_pub(pub), polarssl_proof_pred(pub))(random__) { call(); }
    {duplicate_lemma_function_pointer_chunk(polarssl_bad_random_is_public);};
  }
}

lemma void retreive_polarssl_bad_key_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_bad_key_is_public(_, polarssl_pub(pub), 
                                            polarssl_proof_pred(pub));
{
  {
    lemma void crypto_polarssl_bad_key_is_public(polarssl_cryptogram key)
      requires  polarssl_proof_pred(pub)() &*&
                key == polarssl_symmetric_key(?p__, ?c__) &*&
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
    produce_lemma_function_pointer_chunk(crypto_polarssl_bad_key_is_public) :
      polarssl_bad_key_is_public
        (polarssl_pub(pub), polarssl_proof_pred(pub))(key__) { call(); }
    {duplicate_lemma_function_pointer_chunk(polarssl_bad_key_is_public);};
  }
}

lemma void retreive_polarssl_public_key_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_public_key_is_public(_, polarssl_pub(pub), 
                                               polarssl_proof_pred(pub));
{
  {
    lemma void crypto_polarssl_public_key_is_public(polarssl_cryptogram key)
      requires  polarssl_proof_pred(pub)() &*&
                key == polarssl_public_key(?p__, ?c__);
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
    produce_lemma_function_pointer_chunk(crypto_polarssl_public_key_is_public) :
      polarssl_public_key_is_public
        (polarssl_pub(pub), polarssl_proof_pred(pub))(key__) { call(); }
    {duplicate_lemma_function_pointer_chunk(polarssl_public_key_is_public);};
  }
}

lemma void retreive_polarssl_bad_private_key_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_bad_private_key_is_public(_, polarssl_pub(pub), 
                                                    polarssl_proof_pred(pub));
{
  {
    lemma void crypto_polarssl_bad_private_key_is_public( 
                                                        polarssl_cryptogram key)
      requires  polarssl_proof_pred(pub)() &*&
                key == polarssl_private_key(?p__, ?c__) &*&
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
      crypto_polarssl_bad_private_key_is_public) :
      polarssl_bad_private_key_is_public
        (polarssl_pub(pub), polarssl_proof_pred(pub))(key__) { call(); }
    {duplicate_lemma_function_pointer_chunk(
                                          polarssl_bad_private_key_is_public);};
  }
}

lemma void retreive_polarssl_hash_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_hash_is_public(_, polarssl_pub(pub), 
                                         polarssl_proof_pred(pub));
{ 
  {
    lemma void crypto_polarssl_hash_is_public(polarssl_cryptogram hash)
      requires  polarssl_proof_pred(pub)() &*&
                hash == polarssl_hash(?pay) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_public_generated_chars(polarssl_pub(pub))(pay);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(hash);
    {
      close exists<bool>(true);
      leak exists<bool>(true);
      close polarssl_pub(pub)(hash);
      leak polarssl_pub(pub)(hash);
    }
    produce_lemma_function_pointer_chunk(crypto_polarssl_hash_is_public) :
      polarssl_hash_is_public
        (polarssl_pub(pub), polarssl_proof_pred(pub))(hash) { call(); }
    {duplicate_lemma_function_pointer_chunk(polarssl_hash_is_public);};
  }
}

lemma void retreive_polarssl_public_hmac_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_public_hmac_is_public(_, polarssl_pub(pub), 
                                                polarssl_proof_pred(pub));
{
  {
    lemma void crypto_polarssl_public_hmac_is_public(
                                              polarssl_cryptogram hmac)
      requires  polarssl_proof_pred(pub)() &*&
                hmac == polarssl_hmac(?p, ?c, ?pay) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(polarssl_symmetric_key(p, c)) &*&
                [_]polarssl_public_generated_chars(polarssl_pub(pub))(pay);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(hmac);
    {
      close exists<bool>(true);
      leak exists<bool>(true);
      open [_]polarssl_pub(pub)(polarssl_symmetric_key(p, c));
      close polarssl_pub(pub)(hmac);
      leak polarssl_pub(pub)(hmac);
    }
    produce_lemma_function_pointer_chunk
      (crypto_polarssl_public_hmac_is_public) :
        polarssl_public_hmac_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub))(hmac) { call(); }
    {duplicate_lemma_function_pointer_chunk(polarssl_public_hmac_is_public);};
  }
}

lemma void retreive_polarssl_public_encryption_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_public_encryption_is_public(_, polarssl_pub(pub), 
                                                      polarssl_proof_pred(pub));
{
  {
    lemma void crypto_polarssl_public_encryption_is_public(
                                              polarssl_cryptogram encrypted)
      requires  polarssl_proof_pred(pub)() &*&
                encrypted == polarssl_encrypted(?p, ?c, ?pay, ?ent) &*&
                [_]polarssl_pub(pub)(polarssl_symmetric_key(p, c)) &*&
                [_]polarssl_public_generated_chars(polarssl_pub(pub))(pay);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(encrypted);                
    {
      open [_]polarssl_pub(pub)(polarssl_symmetric_key(p, c));
      close polarssl_pub(pub)(encrypted);
      leak polarssl_pub(pub)(encrypted);
    }
    produce_lemma_function_pointer_chunk
      (crypto_polarssl_public_encryption_is_public) :
        polarssl_public_encryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub))(encrypted__) 
    { call(); }
    {duplicate_lemma_function_pointer_chunk(
                                        polarssl_public_encryption_is_public);};
  }
}

lemma void retreive_polarssl_public_decryption_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_public_decryption_is_public(_, polarssl_pub(pub), 
                                                      polarssl_proof_pred(pub));
{
  {
    lemma void crypto_polarssl_public_decryption_is_public(
                                                  polarssl_cryptogram key,
                                                  polarssl_cryptogram encrypted)
      requires  polarssl_proof_pred(pub)() &*&
                key == polarssl_symmetric_key(?p, ?c) &*&
                encrypted == polarssl_encrypted(p, c, ?pay, ?ent) &*&
                [_]polarssl_pub(pub)(key) &*&
                [_]polarssl_pub(pub)(encrypted);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_public_generated_chars(polarssl_pub(pub))(pay);
    {
      open [_]polarssl_pub(pub)(key);
      open [_]polarssl_pub(pub)(encrypted);
    }
    produce_lemma_function_pointer_chunk
      (crypto_polarssl_public_decryption_is_public) :
        polarssl_public_decryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub))(key__, encrypted__) 
    { call(); }
    {duplicate_lemma_function_pointer_chunk(
                                        polarssl_public_decryption_is_public);};
  }
}

lemma void retreive_polarssl_public_auth_encryption_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_public_auth_encryption_is_public(_,
                                     polarssl_pub(pub), polarssl_proof_pred(pub));
{
  {
    lemma void crypto_polarssl_public_auth_encryption_is_public(
                                              polarssl_cryptogram encrypted)
      requires  polarssl_proof_pred(pub)() &*&
                encrypted == 
                           polarssl_auth_encrypted(?p, ?c, ?mac, ?pay, ?ent) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(polarssl_symmetric_key(p, c)) &*&
                [_]polarssl_public_generated_chars(polarssl_pub(pub))(pay);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(encrypted);                
    {
      open [_]polarssl_pub(pub)(polarssl_symmetric_key(p, c));
      close exists<bool>(true);
      leak exists<bool>(true);
      close polarssl_pub(pub)(encrypted);
      leak polarssl_pub(pub)(encrypted);
    }
    produce_lemma_function_pointer_chunk
      (crypto_polarssl_public_auth_encryption_is_public) :
        polarssl_public_auth_encryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub))(encrypted__) 
    { call(); }
    {duplicate_lemma_function_pointer_chunk(
                                   polarssl_public_auth_encryption_is_public);};
  }
}

lemma void retreive_polarssl_public_auth_decryption_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_public_auth_decryption_is_public(_, 
                                     polarssl_pub(pub), polarssl_proof_pred(pub));
{
  {
    lemma void crypto_polarssl_public_auth_decryption_is_public(
                                                  polarssl_cryptogram key,
                                                  polarssl_cryptogram encrypted)
      requires  polarssl_proof_pred(pub)() &*&
                key == polarssl_symmetric_key(?p, ?c) &*&
                encrypted == polarssl_auth_encrypted(p, c, ?mac, ?pay, ?iv) &*&
                [_]polarssl_pub(pub)(key) &*&
                [_]polarssl_pub(pub)(encrypted);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_public_generated_chars(polarssl_pub(pub))(pay);
    {
      open [_]polarssl_pub(pub)(key);
      open [_]polarssl_pub(pub)(encrypted);
      assert [_]exists<bool>(?b);
      if (b)
      {
        assert [_]polarssl_public_generated_chars(polarssl_pub(pub))(pay);
      }
      else
      {
        assert [_]exists<list<char> >(?ent0);
        assert [_]polarssl_pub(pub)(key);
        assert [_]item_constraints_no_collision(?pay0, pay, pub);
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
      (crypto_polarssl_public_auth_decryption_is_public) :
        polarssl_public_auth_decryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub))(key__, encrypted__) 
    { call(); }
    {duplicate_lemma_function_pointer_chunk(
                                   polarssl_public_auth_decryption_is_public);};
  }
}

lemma void retreive_polarssl_public_asym_encryption_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_public_asym_encryption_is_public(_, 
                                     polarssl_pub(pub), polarssl_proof_pred(pub));
{
  {
    lemma void crypto_polarssl_public_asym_encryption_is_public(
                                              polarssl_cryptogram encrypted)
      requires  polarssl_proof_pred(pub)() &*&
                encrypted == polarssl_asym_encrypted(?p, ?c, ?pay, ?ent) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(polarssl_public_key(p, c)) &*&
                [_]polarssl_public_generated_chars(polarssl_pub(pub))(pay);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(encrypted);                
    {
      open [_]polarssl_pub(pub)(polarssl_public_key(p, c));
      close exists<bool>(true);
      leak exists<bool>(true);
      close polarssl_pub(pub)(encrypted);
      leak polarssl_pub(pub)(encrypted);
    }
    produce_lemma_function_pointer_chunk
      (crypto_polarssl_public_asym_encryption_is_public) :
        polarssl_public_asym_encryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub))(encrypted__) 
    { call(); }
    {duplicate_lemma_function_pointer_chunk(
                                   polarssl_public_asym_encryption_is_public);};
  }
}

lemma void retreive_polarssl_public_asym_decryption_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_public_asym_decryption_is_public(_, 
                                     polarssl_pub(pub), polarssl_proof_pred(pub));
{
  {
    lemma void crypto_polarssl_public_asym_decryption_is_public(
                                                  polarssl_cryptogram key,
                                                  polarssl_cryptogram encrypted)
      requires  polarssl_proof_pred(pub)() &*&
                key == polarssl_private_key(?p, ?c) &*&
                encrypted == polarssl_asym_encrypted(p, c, ?pay, ?ent) &*&
                [_]polarssl_pub(pub)(key) &*&
                [_]polarssl_pub(pub)(encrypted);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_public_generated_chars(polarssl_pub(pub))(pay);
    {
      open [_]polarssl_pub(pub)(key);
      open [_]polarssl_pub(pub)(encrypted);
      assert [_]exists<bool>(?b);
      if (b)
      {
        assert [_]polarssl_public_generated_chars(polarssl_pub(pub))(pay);
      }
      else
      {
        assert [_]polarssl_pub(pub)(key);
        assert [_]item_constraints_no_collision(?pay0, pay, pub);
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
      (crypto_polarssl_public_asym_decryption_is_public) :
        polarssl_public_asym_decryption_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub))(key__, encrypted__) 
    { call(); }
    {duplicate_lemma_function_pointer_chunk(
                                   polarssl_public_asym_decryption_is_public);};
  }
}

lemma void retreive_polarssl_public_asym_signature_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_public_asym_signature_is_public(_, 
                                     polarssl_pub(pub), polarssl_proof_pred(pub));
{
  {
    lemma void crypto_polarssl_public_asym_signature_is_public(
                                         polarssl_cryptogram sig)
      requires  polarssl_proof_pred(pub)() &*&
                sig == polarssl_asym_signature(?p, ?c, ?pay, ?ent) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(polarssl_private_key(p, c)) &*&
                [_]polarssl_public_generated_chars(polarssl_pub(pub))(pay);
      ensures   polarssl_proof_pred(pub)() &*&
                [_]polarssl_pub(pub)(sig);
    {
      open [_]polarssl_pub(pub)(polarssl_private_key(p, c));
      close exists<bool>(true);
      leak exists<bool>(true);
      close polarssl_pub(pub)(sig);
      leak polarssl_pub(pub)(sig);
    }
    produce_lemma_function_pointer_chunk
      (crypto_polarssl_public_asym_signature_is_public) :
        polarssl_public_asym_signature_is_public
          (polarssl_pub(pub), polarssl_proof_pred(pub))(sig__) 
    { call(); }
    {duplicate_lemma_function_pointer_chunk(
                                    polarssl_public_asym_signature_is_public);};
  }
}

lemma void retreive_polarssl_proof_obligations()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           polarssl_proof_obligations(polarssl_pub(pub), 
                                      polarssl_proof_pred(pub));
{
  retreive_polarssl_bad_random_is_public();
  retreive_polarssl_bad_key_is_public();
  retreive_polarssl_public_key_is_public();
  retreive_polarssl_bad_private_key_is_public();
  retreive_polarssl_hash_is_public();
  retreive_polarssl_public_hmac_is_public();
  retreive_polarssl_public_encryption_is_public();
  retreive_polarssl_public_decryption_is_public();
  retreive_polarssl_public_auth_encryption_is_public();
  retreive_polarssl_public_auth_decryption_is_public();
  retreive_polarssl_public_asym_encryption_is_public();
  retreive_polarssl_public_asym_decryption_is_public();
  retreive_polarssl_public_asym_signature_is_public();
  
  close polarssl_proof_obligations(polarssl_pub(pub), 
                                   polarssl_proof_pred(pub));
}

@*/