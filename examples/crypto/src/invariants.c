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
                                               proof_obligations, pub);
{
  {
    lemma void crypto_polarssl_bad_random_is_public(polarssl_cryptogram random)
      requires  proof_obligations(pub) &*&
                random == polarssl_random(?p__, ?c__) &*&
                true == bad(p__);
      ensures   proof_obligations(pub) &*&
                [_]polarssl_pub(pub)(random);
    {
      open proof_obligations(pub);
      assert is_public_nonce(?proof, pub);
      proof(nonce_item(p__, c__, 0));
      close proof_obligations(pub);
      close polarssl_pub(pub)(random);
      leak polarssl_pub(pub)(random);
    }
    produce_lemma_function_pointer_chunk(crypto_polarssl_bad_random_is_public) :
      polarssl_bad_random_is_public<predicate(item)>
        (polarssl_pub(pub), proof_obligations, pub)(random__) { call(); }
    {duplicate_lemma_function_pointer_chunk(polarssl_bad_random_is_public);};
  }
}

lemma void retreive_polarssl_bad_key_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_bad_key_is_public(_, polarssl_pub(pub), 
                                            proof_obligations, pub);
{
  {
    lemma void crypto_polarssl_bad_key_is_public(polarssl_cryptogram key)
      requires  proof_obligations(pub) &*&
                key == polarssl_symmetric_key(?p__, ?c__) &*&
                true == bad(p__);
      ensures   proof_obligations(pub) &*&
                [_]polarssl_pub(pub)(key);
    {
      open proof_obligations(pub);
      assert is_public_symmetric_key(?proof, pub);
      proof(symmetric_key_item(p__, c__));
      close proof_obligations(pub);
      close polarssl_pub(pub)(key);
      leak polarssl_pub(pub)(key);
    }
    produce_lemma_function_pointer_chunk(crypto_polarssl_bad_key_is_public) :
      polarssl_bad_key_is_public<predicate(item)>
        (polarssl_pub(pub), proof_obligations, pub)(key__) { call(); }
    {duplicate_lemma_function_pointer_chunk(polarssl_bad_key_is_public);};
  }
}

lemma void retreive_polarssl_public_key_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_public_key_is_public(_, polarssl_pub(pub), 
                                               proof_obligations, pub);
{
  {
    lemma void crypto_polarssl_public_key_is_public(polarssl_cryptogram key)
      requires  proof_obligations(pub) &*&
                key == polarssl_public_key(?p__, ?c__);
      ensures   proof_obligations(pub) &*&
                [_]polarssl_pub(pub)(key);
    {
      open proof_obligations(pub);
      assert is_public_public_key(?proof, pub);
      proof(public_key_item(p__, c__));
      close proof_obligations(pub);      
      close polarssl_pub(pub)(key);
      leak polarssl_pub(pub)(key);
    }
    produce_lemma_function_pointer_chunk(crypto_polarssl_public_key_is_public) :
      polarssl_public_key_is_public<predicate(item)>
        (polarssl_pub(pub), proof_obligations, pub)(key__) { call(); }
    {duplicate_lemma_function_pointer_chunk(polarssl_public_key_is_public);};
  }
}

lemma void retreive_polarssl_bad_private_key_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_bad_private_key_is_public(_, polarssl_pub(pub), 
                                                    proof_obligations, pub);
{
  {
    lemma void crypto_polarssl_bad_private_key_is_public( 
                                                        polarssl_cryptogram key)
      requires  proof_obligations(pub) &*&
                key == polarssl_private_key(?p__, ?c__) &*&
                true == bad(p__);
      ensures   proof_obligations(pub) &*&
                [_]polarssl_pub(pub)(key);
    {
      open proof_obligations(pub);
      assert is_public_private_key(?proof, pub);
      proof(private_key_item(p__, c__));
      close proof_obligations(pub);
      close polarssl_pub(pub)(key);
      leak polarssl_pub(pub)(key);
    }
    produce_lemma_function_pointer_chunk(
      crypto_polarssl_bad_private_key_is_public) :
      polarssl_bad_private_key_is_public<predicate(item)>
        (polarssl_pub(pub), proof_obligations, pub)(key__) { call(); }
    {duplicate_lemma_function_pointer_chunk(
                                          polarssl_bad_private_key_is_public);};
  }
}

lemma void retreive_polarssl_hash_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_hash_is_public(_, polarssl_pub(pub), 
                                         proof_obligations, pub);
{ 
  {
    lemma void crypto_polarssl_hash_is_public(polarssl_cryptogram hash,
                                              list<polarssl_cryptogram> cgs_pay)
      requires  proof_obligations(pub) &*&
                hash == polarssl_hash(?pay) &*&
                length(pay) <= INT_MAX &*&
                polarssl_cryptograms_in_chars_upper_bound(pay, cgs_pay) &&
                subset(cgs_pay, polarssl_generated_public_cryptograms(
                                                            polarssl_pub(pub)));
      ensures   proof_obligations(pub) &*&
                [_]polarssl_pub(pub)(hash);
    {
      close exists<bool>(true);
      leak exists<bool>(true);
      polarssl_cryptograms_in_chars_upper_bound_subset(pay, cgs_pay,
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      polarssl_cryptograms_in_chars_upper_bound_from(pay, 
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      close polarssl_pub(pub)(hash);
      leak polarssl_pub(pub)(hash);
    }
    produce_lemma_function_pointer_chunk(crypto_polarssl_hash_is_public) :
      polarssl_hash_is_public<predicate(item)>
        (polarssl_pub(pub), proof_obligations, pub)(hash, cgs_pay) { call(); }
    {duplicate_lemma_function_pointer_chunk(polarssl_hash_is_public);};
  }
}

lemma void retreive_polarssl_public_hmac_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_public_hmac_is_public(_, polarssl_pub(pub), 
                                                proof_obligations, pub);
{
  {
    lemma void crypto_polarssl_public_hmac_is_public(
                                              polarssl_cryptogram hmac,
                                              list<polarssl_cryptogram> cgs_pay)
      requires  proof_obligations(pub) &*&
                hmac == polarssl_hmac(?p, ?c, ?pay) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(polarssl_symmetric_key(p, c)) &*&
                polarssl_cryptograms_in_chars_upper_bound(pay, cgs_pay) &&
                subset(cgs_pay, polarssl_generated_public_cryptograms(
                                                            polarssl_pub(pub)));
      ensures   proof_obligations(pub) &*&
                [_]polarssl_pub(pub)(hmac);
    {
      close exists<bool>(true);
      leak exists<bool>(true);
      open [_]polarssl_pub(pub)(polarssl_symmetric_key(p, c));
      polarssl_cryptograms_in_chars_upper_bound_subset(pay, cgs_pay,
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      polarssl_cryptograms_in_chars_upper_bound_from(pay, 
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      close polarssl_pub(pub)(hmac);
      leak polarssl_pub(pub)(hmac);
    }
    produce_lemma_function_pointer_chunk
      (crypto_polarssl_public_hmac_is_public) :
        polarssl_public_hmac_is_public<predicate(item)>
          (polarssl_pub(pub), proof_obligations, pub)(hmac, cgs_pay) { call(); }
    {duplicate_lemma_function_pointer_chunk(polarssl_public_hmac_is_public);};
  }
}

lemma void retreive_polarssl_public_encryption_is_public()
  nonghost_callers_only
  requires proof_obligations(?pub);
  ensures  proof_obligations(pub) &*&
           is_polarssl_public_encryption_is_public(_, polarssl_pub(pub), 
                                                      proof_obligations, pub);
{
  {
    lemma void crypto_polarssl_public_encryption_is_public(
                                              polarssl_cryptogram encrypted, 
                                              list<polarssl_cryptogram> cgs_pay)
      requires  proof_obligations(pub) &*&
                encrypted == polarssl_encrypted(?p, ?c, ?pay, ?ent) &*&
                [_]polarssl_pub(pub)(polarssl_symmetric_key(p, c)) &*&
                polarssl_cryptograms_in_chars_upper_bound(pay, cgs_pay) &&
                subset(cgs_pay, polarssl_generated_public_cryptograms(
                                                            polarssl_pub(pub)));
      ensures   proof_obligations(pub) &*&
                [_]polarssl_pub(pub)(encrypted);                
    {
      open [_]polarssl_pub(pub)(polarssl_symmetric_key(p, c));
      polarssl_cryptograms_in_chars_upper_bound_subset(pay, cgs_pay,
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      polarssl_cryptograms_in_chars_upper_bound_from(pay, 
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      close polarssl_pub(pub)(encrypted);
      leak polarssl_pub(pub)(encrypted);
    }
    produce_lemma_function_pointer_chunk
      (crypto_polarssl_public_encryption_is_public) :
        polarssl_public_encryption_is_public<predicate(item)>
          (polarssl_pub(pub), proof_obligations, pub)(encrypted__, cgs_pay__) 
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
                                                      proof_obligations, pub);
{
  {
    lemma void crypto_polarssl_public_decryption_is_public(
                                                  polarssl_cryptogram key,
                                                  polarssl_cryptogram encrypted)
      requires  proof_obligations(pub) &*&
                key == polarssl_symmetric_key(?p, ?c) &*&
                encrypted == polarssl_encrypted(p, c, ?pay, ?ent) &*&
                [_]polarssl_pub(pub)(key) &*&
                [_]polarssl_pub(pub)(encrypted);
      ensures   proof_obligations(pub) &*&
                true == subset(polarssl_cryptograms_in_chars(pay), 
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
    {
      open [_]polarssl_pub(pub)(key);
      open [_]polarssl_pub(pub)(encrypted);
      assert true == subset(polarssl_cryptograms_in_chars(pay),
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
    }
    produce_lemma_function_pointer_chunk
      (crypto_polarssl_public_decryption_is_public) :
        polarssl_public_decryption_is_public<predicate(item)>
          (polarssl_pub(pub), proof_obligations, pub)(key__, encrypted__) 
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
                                     polarssl_pub(pub), proof_obligations, pub);
{
  {
    lemma void crypto_polarssl_public_auth_encryption_is_public(
                                              polarssl_cryptogram encrypted, 
                                              list<polarssl_cryptogram> cgs_pay)
      requires  proof_obligations(pub) &*&
                encrypted == 
                           polarssl_auth_encrypted(?p, ?c, ?mac, ?pay, ?ent) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(polarssl_symmetric_key(p, c)) &*&
                polarssl_cryptograms_in_chars_upper_bound(pay, cgs_pay) &&
                subset(cgs_pay, polarssl_generated_public_cryptograms(
                                                            polarssl_pub(pub)));
      ensures   proof_obligations(pub) &*&
                [_]polarssl_pub(pub)(encrypted);                
    {
      open [_]polarssl_pub(pub)(polarssl_symmetric_key(p, c));
      polarssl_cryptograms_in_chars_upper_bound_subset(pay, cgs_pay,
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      polarssl_cryptograms_in_chars_upper_bound_from(pay, 
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      close exists<bool>(true);
      leak exists<bool>(true);
      close polarssl_pub(pub)(encrypted);
      leak polarssl_pub(pub)(encrypted);
    }
    produce_lemma_function_pointer_chunk
      (crypto_polarssl_public_auth_encryption_is_public) :
        polarssl_public_auth_encryption_is_public<predicate(item)>
          (polarssl_pub(pub), proof_obligations, pub)(encrypted__, cgs_pay__) 
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
                                     polarssl_pub(pub), proof_obligations, pub);
{
  {
    lemma void crypto_polarssl_public_auth_decryption_is_public(
                                                  polarssl_cryptogram key,
                                                  polarssl_cryptogram encrypted)
      requires  proof_obligations(pub) &*&
                key == polarssl_symmetric_key(?p, ?c) &*&
                encrypted == polarssl_auth_encrypted(p, c, ?mac, ?pay, ?iv) &*&
                [_]polarssl_pub(pub)(key) &*&
                [_]polarssl_pub(pub)(encrypted);
      ensures   proof_obligations(pub) &*&
                true == subset(polarssl_cryptograms_in_chars(pay), 
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
    {
      open [_]polarssl_pub(pub)(key);
      open [_]polarssl_pub(pub)(encrypted);
      assert [_]exists<bool>(?b);
      if (b)
      {
        assert true == subset(polarssl_cryptograms_in_chars(pay),
                 polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      }
      else
      {
        assert [_]exists<list<char> >(?ent0);
        assert [_]polarssl_pub(pub)(key);
        assert [_]item_constraints_no_collision(?pay0, pay, pub);
        item enc = symmetric_encrypted_item(p, c, some(pay0), ent0);
        assert [_]pub(enc);
        assert drop(GCM_ENT_SIZE, ent0) == cons(length(mac), append(mac, iv));
        
        open proof_obligations(pub);
        assert is_public_symmetric_decrypted(?proof, pub);
        proof(enc);
        close proof_obligations(pub);
        assert [_]pub(pay0);
        serialize_item(pay0);
        polarssl_cryptograms_in_chars_upper_bound_from(pay, 
                       polarssl_generated_public_cryptograms(polarssl_pub(pub)));        
      }
    }
    produce_lemma_function_pointer_chunk
      (crypto_polarssl_public_auth_decryption_is_public) :
        polarssl_public_auth_decryption_is_public<predicate(item)>
          (polarssl_pub(pub), proof_obligations, pub)(key__, encrypted__) 
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
                                     polarssl_pub(pub), proof_obligations, pub);
{
  {
    lemma void crypto_polarssl_public_asym_encryption_is_public(
                                              polarssl_cryptogram encrypted, 
                                              list<polarssl_cryptogram> cgs_pay)
      requires  proof_obligations(pub) &*&
                encrypted == polarssl_asym_encrypted(?p, ?c, ?pay, ?ent) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(polarssl_public_key(p, c)) &*&
                polarssl_cryptograms_in_chars_upper_bound(pay, cgs_pay) &&
                subset(cgs_pay, polarssl_generated_public_cryptograms(
                                                            polarssl_pub(pub)));
      ensures   proof_obligations(pub) &*&
                [_]polarssl_pub(pub)(encrypted);                
    {
      open [_]polarssl_pub(pub)(polarssl_public_key(p, c));
      polarssl_cryptograms_in_chars_upper_bound_subset(pay, cgs_pay,
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      polarssl_cryptograms_in_chars_upper_bound_from(pay, 
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      close exists<bool>(true);
      leak exists<bool>(true);
      close polarssl_pub(pub)(encrypted);
      leak polarssl_pub(pub)(encrypted);
    }
    produce_lemma_function_pointer_chunk
      (crypto_polarssl_public_asym_encryption_is_public) :
        polarssl_public_asym_encryption_is_public<predicate(item)>
          (polarssl_pub(pub), proof_obligations, pub)(encrypted__, cgs_pay__) 
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
                                     polarssl_pub(pub), proof_obligations, pub);
{
  {
    lemma void crypto_polarssl_public_asym_decryption_is_public(
                                                  polarssl_cryptogram key,
                                                  polarssl_cryptogram encrypted)
      requires  proof_obligations(pub) &*&
                key == polarssl_private_key(?p, ?c) &*&
                encrypted == polarssl_asym_encrypted(p, c, ?pay, ?ent) &*&
                [_]polarssl_pub(pub)(key) &*&
                [_]polarssl_pub(pub)(encrypted);
      ensures   proof_obligations(pub) &*&
                true == subset(polarssl_cryptograms_in_chars(pay),
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));          
    {
      open [_]polarssl_pub(pub)(key);
      open [_]polarssl_pub(pub)(encrypted);
      assert [_]exists<bool>(?b);
      if (b)
      {
        assert true == subset(polarssl_cryptograms_in_chars(pay),
                 polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      }
      else
      {
        assert [_]polarssl_pub(pub)(key);
        assert [_]item_constraints_no_collision(?pay0, pay, pub);
        item enc = asymmetric_encrypted_item(p, c, some(pay0), ent);
        assert [_]pub(enc);
        
        open proof_obligations(pub);
        assert is_public_asymmetric_decrypted(?proof, pub);
        proof(enc);
        close proof_obligations(pub);
        assert [_]pub(pay0);
        serialize_item(pay0);
        polarssl_cryptograms_in_chars_upper_bound_from(pay, 
                       polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      }
    }
    produce_lemma_function_pointer_chunk
      (crypto_polarssl_public_asym_decryption_is_public) :
        polarssl_public_asym_decryption_is_public<predicate(item)>
          (polarssl_pub(pub), proof_obligations, pub)(key__, encrypted__) 
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
                                     polarssl_pub(pub), proof_obligations, pub);
{
  {
    lemma void crypto_polarssl_public_asym_signature_is_public(
                                         polarssl_cryptogram sig,
                                         list<polarssl_cryptogram> cgs_pay)
      requires  proof_obligations(pub) &*&
                sig == polarssl_asym_signature(?p, ?c, ?pay, ?ent) &*&
                length(pay) <= INT_MAX &*&
                [_]polarssl_pub(pub)(polarssl_private_key(p, c)) &*&
                polarssl_cryptograms_in_chars_upper_bound(pay, cgs_pay) &&
                subset(cgs_pay, polarssl_generated_public_cryptograms(
                                                            polarssl_pub(pub)));
      ensures   proof_obligations(pub) &*&
                [_]polarssl_pub(pub)(sig);
    {
      open [_]polarssl_pub(pub)(polarssl_private_key(p, c));
      polarssl_cryptograms_in_chars_upper_bound_subset(pay, cgs_pay,
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      polarssl_cryptograms_in_chars_upper_bound_from(pay, 
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      close exists<bool>(true);
      leak exists<bool>(true);
      close polarssl_pub(pub)(sig);
      leak polarssl_pub(pub)(sig);
    }
    produce_lemma_function_pointer_chunk
      (crypto_polarssl_public_asym_signature_is_public) :
        polarssl_public_asym_signature_is_public<predicate(item)>
          (polarssl_pub(pub), proof_obligations, pub)(sig__, cgs_pay__) 
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
                                      proof_obligations, pub);
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
                                   proof_obligations, pub);
}

@*/