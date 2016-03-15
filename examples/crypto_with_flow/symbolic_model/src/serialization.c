#include "serialization.h"

#include "principal_ids.h"
#include "item_constraints.h"

/*@

#define SERIALIZE_PAY \
  switch(pay0) \
  { \
    case some(pay1): \
      close exists(false); \
      leak exists(false); \
    case none: \
      close exists(true); \
      leak exists(true); \
  }

#define SERIALIZE_DEFAULT(ITEM, TAG, CG, PAY) \
  open [_]item_constraints(ITEM, cs, pub); \
  assert [_]ic_parts(ITEM)(?tag_cs, ?cont_cs); \
  assert [_]ic_cg(ITEM)(cont_cs, ?cg) &*& col || cont_cs == chars_for_cg(cg); \
  assert cg == CG; \
  if (PAY) {SERIALIZE_PAY} \
  if (!col) \
  { \
    close polarssl_pub(pub)(cg); \
    leak polarssl_pub(pub)(cg); \
    public_generated(polarssl_pub(pub), cg); \
    public_generated_join(polarssl_pub(pub), full_tag(TAG), cont_cs); \
  }

lemma void serialize_data(list<char> data)
  requires proof_obligations(?pub) &*&
           [_]item_constraints(?datai, ?cs, pub) &*&
           datai == data_item(data);
  ensures  proof_obligations(pub) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
{
  open [_]item_constraints(datai, cs, pub);
}

lemma void serialize_pair(list<char> cs, list<char> f_cs, list<char> s_cs)
  requires proof_obligations(?pub) &*&
           [_]public_generated(polarssl_pub(pub))(full_tag(TAG_PAIR)) &*&
           [_]public_generated(polarssl_pub(pub))(chars_of_unbounded_int(length(f_cs))) &*&
           [_]public_generated(polarssl_pub(pub))(f_cs) &*&
           [_]public_generated(polarssl_pub(pub))(s_cs) &*&
           cs == append(full_tag(TAG_PAIR),
                        append(chars_of_unbounded_int(length(f_cs)),
                               append(f_cs, s_cs)));
  ensures  proof_obligations(pub) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
{
  int length_f = length(f_cs);
  list<char> length_f_cs = chars_of_unbounded_int(length(f_cs));
  public_generated_join(polarssl_pub(pub), full_tag(TAG_PAIR), length_f_cs);
  public_generated_join(polarssl_pub(pub), append(full_tag(TAG_PAIR), length_f_cs), f_cs);
  public_generated_join(polarssl_pub(pub), append(append(full_tag(TAG_PAIR), length_f_cs), f_cs), s_cs);
  append_assoc(append(full_tag(TAG_PAIR), length_f_cs), f_cs, s_cs);
  append_assoc(full_tag(TAG_PAIR), append(length_f_cs, f_cs), s_cs);
  append_assoc(full_tag(TAG_PAIR), length_f_cs, append(f_cs, s_cs));
}

lemma void serialize_nonce(int p0, int c0, char inc0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints(?nonce, ?cs, pub) &*&
           nonce == nonce_item(p0, c0, inc0) &*& [_]pub(nonce);
  ensures  proof_obligations(pub) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
{
  item nonce0 = nonce_item(p0, c0, 0);
  open proof_obligations(pub);
  assert is_public_incremented_nonce(?proof, pub);
  proof(nonce, nonce0);
  close proof_obligations(pub);

  assert [_]pub(nonce);
  assert [_]pub(nonce0);
  open [_]item_constraints(nonce, cs, pub);
  assert [_]ic_parts(nonce)(?cs_tag, ?cs_cont);
  cryptogram pnonce = cg_nonce(p0, c0);
  cg_constraints(pnonce);
  close polarssl_pub(pub)(pnonce);
  leak polarssl_pub(pub)(pnonce);
  list<char> cs_cg = chars_for_cg(pnonce);
  if (!col)
  {
    public_generated(polarssl_pub(pub), pnonce);
    public_generated_join(polarssl_pub(pub), cons(inc0, nil), cs_cg);
    public_generated_join(polarssl_pub(pub), cs_tag, cons(inc0, cs_cg));
  }
}

lemma void serialize_hash(option<item> pay0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints(?hash, ?cs, pub) &*&
           hash == hash_item(pay0) &*& [_]pub(hash);
  ensures  proof_obligations(pub) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
{
  SERIALIZE_DEFAULT(hash, TAG_HASH, cg_hash(?cs_pay), true)
}

lemma void serialize_symmetric_key(int p0, int c0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints(?key, ?cs, pub) &*&
           key == symmetric_key_item(p0, c0) &*& [_]pub(key);
  ensures  proof_obligations(pub) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
{
  SERIALIZE_DEFAULT(key, TAG_SYMMETRIC_KEY, cg_symmetric_key(p0, c0), false)
}

lemma void serialize_public_key(int p0, int c0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints(?key, ?cs, pub) &*&
           key == public_key_item(p0, c0) &*& [_]pub(key);
  ensures  proof_obligations(pub) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
{
  SERIALIZE_DEFAULT(key, TAG_PUBLIC_KEY, cg_public_key(p0, c0), false)
}

lemma void serialize_private_key(int p0, int c0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints(?key, ?cs, pub) &*&
           key == private_key_item(p0, c0) &*& [_]pub(key);
  ensures  proof_obligations(pub) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
{
  SERIALIZE_DEFAULT(key, TAG_PRIVATE_KEY, cg_private_key(p0, c0), false)
}

lemma void serialize_hmac(int p0, int c0, option<item> pay0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints(?hmac, ?cs, pub) &*&
           hmac == hmac_item(p0, c0, pay0) &*& [_]pub(hmac);
  ensures  proof_obligations(pub) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
{
  SERIALIZE_DEFAULT(hmac, TAG_HMAC, cg_hmac(p0, c0, ?cs_pay), true)
}

lemma void serialize_symmetric_encrypted(int p0, int c0,
                                          option<item> pay0, list<char> ent0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints(?enc, ?cs, pub) &*&
           enc == symmetric_encrypted_item(p0, c0, pay0, ent0) &*& [_]pub(enc);
  ensures  proof_obligations(pub) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
{
  open [_]item_constraints(enc, cs, pub);
  assert [_]ic_sym_enc(enc)(?iv0, ?cs_cg0);
  assert [_]ic_parts(enc)(?tag_cs, ?cont_cs);
  list<char> iv0_cs = take(GCM_IV_SIZE, ent0);
  assert iv0 == drop(GCM_IV_SIZE, ent0);
  assert ent0 == append(iv0_cs, iv0);
  list<char> cs_cg = drop(GCM_IV_SIZE, cont_cs);
  assert cont_cs == append(iv0_cs, cs_cg);
  append_assoc(tag_cs, iv0_cs, cs_cg);
  if (!col)
  {
    cryptogram penc;
    switch(pay0)
    {
      case some(pay1):
        assert [_]well_formed_item_chars(enc)(?cs_pay0);
        assert [_]item_constraints(pay1, cs_pay0, pub);
        penc = cg_auth_encrypted(p0, c0, cs_pay0, iv0);
        close exists(ent0);
        leak exists(ent0);
        close exists(false);
        leak exists(false);
      case none:
        assert [_]ill_formed_item_chars(enc)(?cs_pay0);
        penc = cg_auth_encrypted(p0, c0, cs_pay0, iv0);
        cg_constraints(penc);
        close exists(true);
        leak exists(true);
    }
    close polarssl_pub(pub)(penc);
    leak polarssl_pub(pub)(penc);
    public_generated(polarssl_pub(pub), penc);
    public_generated_join(polarssl_pub(pub), 
                          full_tag(TAG_SYMMETRIC_ENC), iv0_cs);
    public_generated_join(polarssl_pub(pub),
                          append(full_tag(TAG_SYMMETRIC_ENC), iv0_cs), cs_cg);
  }
}

lemma void serialize_asymmetric_encrypted(int p0, int c0,
                                          option<item> pay0, list<char> ent0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints(?enc, ?cs, pub) &*&
           enc == asymmetric_encrypted_item(p0, c0, pay0, ent0) &*& [_]pub(enc);
  ensures  proof_obligations(pub) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
{
  SERIALIZE_DEFAULT(enc, TAG_ASYMMETRIC_ENC, cg_asym_encrypted(p0, c0, ?cs_pay, ent0), true)
}

lemma void serialize_asymmetric_signature(int p0, int c0,
                                          option<item> pay0, list<char> ent0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints(?sig, ?cs, pub) &*&
           sig == asymmetric_signature_item(p0, c0, pay0, ent0) &*& [_]pub(sig);
  ensures  proof_obligations(pub) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
{
  SERIALIZE_DEFAULT(sig, TAG_ASYMMETRIC_SIG, cg_asym_signature(p0, c0, ?cs_pay, ent0), true)
}

lemma void serialize_item(item i)
  requires proof_obligations(?pub) &*&
           [_]item_constraints(i, ?cs, pub) &*&
           [_]pub(i);
  ensures  proof_obligations(pub) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
{
  switch (i)
  {
    case data_item(d0):
      serialize_data(d0);
    case pair_item(first0, second0):
      open [_]item_constraints(i, cs, pub);
      assert [_]item_constraints(first0, ?f_cs, pub);
      assert [_]item_constraints(second0, ?s_cs, pub);
      open proof_obligations(pub);
      assert is_public_pair_decompose(?proof, pub);
      proof(i);
      close proof_obligations(pub);
      assert [_]pub(first0);
      assert [_]pub(second0);
      serialize_item(first0);
      serialize_item(second0);
      serialize_pair(cs, f_cs, s_cs);
    case nonce_item(p0, c0, inc0):
      serialize_nonce(p0, c0, inc0);
    case hash_item(pay0):
      serialize_hash(pay0);
    case symmetric_key_item(p0, c0):
      serialize_symmetric_key(p0, c0);
    case public_key_item(p0, c0):
      serialize_public_key(p0, c0);
    case private_key_item(p0, c0):
      serialize_private_key(p0, c0);
    case hmac_item(p0, c0, pay0):
      serialize_hmac(p0, c0, pay0);
    case symmetric_encrypted_item(p0, c0, pay0, ent0):
      serialize_symmetric_encrypted(p0, c0, pay0, ent0);
    case asymmetric_encrypted_item(p0, c0, pay0, ent0):
      serialize_asymmetric_encrypted(p0, c0, pay0, ent0);
    case asymmetric_signature_item(p0, c0, pay0, ent0):
      serialize_asymmetric_signature(p0, c0, pay0, ent0);
  }
}

lemma void retreive_proof_obligations()
  nonghost_callers_only
  requires [?f]world(?pub, ?key_clsfy);
  ensures  [f]world(pub, key_clsfy) &*& proof_obligations(pub);
{
  open  [f]world(pub, key_clsfy);
  open  [f]proof_obligations(pub);

  duplicate_lemma_function_pointer_chunk(public_collision);
  duplicate_lemma_function_pointer_chunk(public_none_payload_item);
  duplicate_lemma_function_pointer_chunk(public_data);
  duplicate_lemma_function_pointer_chunk(public_pair_compose);
  duplicate_lemma_function_pointer_chunk(public_pair_decompose);
  duplicate_lemma_function_pointer_chunk(public_nonce);
  duplicate_lemma_function_pointer_chunk(public_incremented_nonce);
  duplicate_lemma_function_pointer_chunk(public_hash);
  duplicate_lemma_function_pointer_chunk(public_symmetric_key);
  duplicate_lemma_function_pointer_chunk(public_public_key);
  duplicate_lemma_function_pointer_chunk(public_private_key);
  duplicate_lemma_function_pointer_chunk(public_hmac);
  duplicate_lemma_function_pointer_chunk(public_symmetric_encrypted);
  duplicate_lemma_function_pointer_chunk(public_symmetric_encrypted_entropy);
  duplicate_lemma_function_pointer_chunk(public_symmetric_decrypted);
  duplicate_lemma_function_pointer_chunk(public_asymmetric_encrypted);
  duplicate_lemma_function_pointer_chunk(public_asymmetric_encrypted_entropy);
  duplicate_lemma_function_pointer_chunk(public_asymmetric_decrypted);
  duplicate_lemma_function_pointer_chunk(public_asymmetric_signature);
  close proof_obligations(pub);

  close [f]proof_obligations(pub);
  close [f]world(pub, key_clsfy);
}

@*/

int serialize_to_public_message(char** dest, struct item* item)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               [?f1]item(item, ?i, pub) &*& pointer(dest, _) &*&
               [_]pub(i); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               [f1]item(item, i, pub) &*& pointer(dest, ?d) &*&
               malloc_block(d, result) &*& result > 1 &*&
               chars(d, result, ?cs) &*&
               [_]item_constraints(i, cs, pub); @*/
{
  int size;
  char* temp;
  //@ open [f1]item(item, i, pub);
  //@ assert [f1]item->content |-> ?cont;
  size = item->size;
  //@ assert [f1]crypto_chars(secret, cont, size, ?cs);

  temp = malloc_wrapper(size);
  memcpy(temp, item->content, (unsigned int) size);
  *dest = temp;

  //@ open [f0]world(pub, key_clsfy);
  //@ close [f0]world(pub, key_clsfy);
  //@ retreive_proof_obligations();
  //@ assert [_]item_constraints(i, cs, pub);
  //@ serialize_item(i);
  //@ public_crypto_chars(temp, size);
  //@ leak proof_obligations(pub);
  //@ close [f1]item(item, i, pub);

  return size;
}
