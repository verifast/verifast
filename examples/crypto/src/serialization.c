#include "serialization.h"

#include "principals.h"
#include "item_constraints.h"

/*@ 

lemma void collision_public(predicate(item) pub, list<char> cs)
  requires true == collision_in_run();
  ensures  [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
{
  polarssl_public_generated_chars_assume(polarssl_pub(pub), cs); //Checked
}

lemma void serialize_data(list<char> data)
  requires proof_obligations(?pub) &*&
           [_]item_constraints_no_collision(?datai, ?cs, pub) &*&
           datai == data_item(data);
  ensures  proof_obligations(pub) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
{
  open [_]item_constraints_no_collision(datai, cs, pub);
  assert cs == cons('a', data);
  polarssl_public_generated_chars_assume(polarssl_pub(pub), cons('a', data)); //Checked
}

lemma void serialize_pair(list<char> cs, list<char> f_cs, list<char> s_cs)
  requires proof_obligations(?pub) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(f_cs) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(s_cs) &*&
           cs == cons('b', append(chars_of_unbounded_int(length(f_cs)), 
                                  append(f_cs, s_cs)));
  ensures  proof_obligations(pub) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
{
  int length_f = length(f_cs);
  list<char> length_f_cs = chars_of_unbounded_int(length(f_cs));
  polarssl_public_generated_chars_assume(polarssl_pub(pub), cons('b', length_f_cs)); //Checked
  polarssl_public_generated_chars_join(
                               polarssl_pub(pub), cons('b', length_f_cs), f_cs);
  polarssl_public_generated_chars_join(
                 polarssl_pub(pub), append(cons('b', length_f_cs), f_cs), s_cs);
  append_assoc(length_f_cs, f_cs, s_cs);
}

lemma void serialize_nonce(int p0, int c0, char inc0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints_no_collision(?nonce, ?cs, pub) &*&
           nonce == nonce_item(p0, c0, inc0) &*& [_]pub(nonce);
  ensures  proof_obligations(pub) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
{
  item nonce0 = nonce_item(p0, c0, 0);
  open proof_obligations(pub);
  assert is_public_incremented_nonce(?proof, pub);
  proof(nonce, nonce0);
  close proof_obligations(pub);
  
  assert [_]pub(nonce);
  assert [_]pub(nonce0);
  
  open [_]item_constraints_no_collision(nonce, cs, pub);
  assert cs == cons('c', cons(inc0, ?cs_cg));
  polarssl_cryptogram pnonce = polarssl_random(p0, c0);
  polarssl_cryptogram_constraints(cs_cg, pnonce);
  close polarssl_pub(pub)(pnonce);
  leak polarssl_pub(pub)(pnonce);
  polarssl_public_generated_cryptogram_chars(polarssl_pub(pub), pnonce);
  polarssl_public_generated_chars_assume(polarssl_pub(pub), cons('c', cons(inc0, nil))); //Checked
  polarssl_public_generated_chars_join(
                          polarssl_pub(pub), cons('c', cons(inc0, nil)), cs_cg);
}

lemma void serialize_hash(option<item> pay0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints_no_collision(?hash, ?cs, pub) &*&
           hash == hash_item(pay0) &*& [_]pub(hash);
  ensures  proof_obligations(pub) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
{
  open [_]item_constraints_no_collision(hash, cs, pub);
  assert cs == cons('d', ?cs_cg);
  
  polarssl_cryptogram phash;
  switch(pay0)
  {
    case some(pay1):
      assert [_]item_constraints_no_collision(pay1, ?cs_pay0, pub);
      phash = polarssl_hash(cs_pay0);
      close exists(false);
      leak exists(false);
    case none:
      assert [_]ill_formed_item_chars(hash)(?cs_pay0);
      phash = polarssl_hash(cs_pay0);
      polarssl_cryptogram_constraints(cs_cg, phash);
      close exists(true);
      leak exists(true);
  }
  close polarssl_pub(pub)(phash);
  leak polarssl_pub(pub)(phash);
  polarssl_public_generated_cryptogram_chars(polarssl_pub(pub), phash);
  polarssl_public_generated_chars_assume(polarssl_pub(pub), cons('d', nil)); //Checked
  polarssl_public_generated_chars_join(
                                      polarssl_pub(pub), cons('d', nil), cs_cg);                                      
}


lemma void serialize_symmetric_key(int p0, int c0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints_no_collision(?key, ?cs, pub) &*&
           key == symmetric_key_item(p0, c0) &*& [_]pub(key);
  ensures  proof_obligations(pub) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
{
  open [_]item_constraints_no_collision(key, cs, pub);
  assert cs == cons('e', ?cs_cg);
  polarssl_cryptogram pkey = polarssl_symmetric_key(p0, c0);
  polarssl_cryptogram_constraints(cs_cg, pkey);
  close polarssl_pub(pub)(pkey);
  leak polarssl_pub(pub)(pkey);
  polarssl_public_generated_cryptogram_chars(polarssl_pub(pub), pkey);
  polarssl_public_generated_chars_assume(polarssl_pub(pub), cons('e', nil)); //Checked
  polarssl_public_generated_chars_join(
                                      polarssl_pub(pub), cons('e', nil), cs_cg);
}

lemma void serialize_public_key(int p0, int c0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints_no_collision(?key, ?cs, pub) &*&
           key == public_key_item(p0, c0) &*& [_]pub(key);
  ensures  proof_obligations(pub) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
{
  open [_]item_constraints_no_collision(key, cs, pub);
  assert cs == cons('f', ?cs_cg);
  polarssl_cryptogram pkey = polarssl_public_key(p0, c0);
  polarssl_cryptogram_constraints(cs_cg, pkey);
  close polarssl_pub(pub)(pkey);
  leak polarssl_pub(pub)(pkey);
  polarssl_public_generated_cryptogram_chars(polarssl_pub(pub), pkey);
  polarssl_public_generated_chars_assume(polarssl_pub(pub), cons('f', nil)); //Checked
  polarssl_public_generated_chars_join(
                                      polarssl_pub(pub), cons('f', nil), cs_cg);
}

lemma void serialize_private_key(int p0, int c0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints_no_collision(?key, ?cs, pub) &*&
           key == private_key_item(p0, c0) &*& [_]pub(key);
  ensures  proof_obligations(pub) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
{
  open [_]item_constraints_no_collision(key, cs, pub);
  assert cs == cons('g', ?cs_cg);
  polarssl_cryptogram pkey = polarssl_private_key(p0, c0);
  polarssl_cryptogram_constraints(cs_cg, pkey);
  close polarssl_pub(pub)(pkey);
  leak polarssl_pub(pub)(pkey);
  polarssl_public_generated_cryptogram_chars(polarssl_pub(pub), pkey);
  polarssl_public_generated_chars_assume(polarssl_pub(pub), cons('g', nil)); //Checked
  polarssl_public_generated_chars_join(
                                      polarssl_pub(pub), cons('g', nil), cs_cg);
}

lemma void serialize_hmac(int p0, int c0, option<item> pay0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints_no_collision(?hmac, ?cs, pub) &*&
           hmac == hmac_item(p0, c0, pay0) &*& [_]pub(hmac);
  ensures  proof_obligations(pub) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
{
  open [_]item_constraints_no_collision(hmac, cs, pub);
  assert cs == cons('h', ?cs_cg);
  
  polarssl_cryptogram phmac;
  switch(pay0)
  {
    case some(pay1):
      assert [_]item_constraints_no_collision(pay1, ?cs_pay0, pub);
      phmac = polarssl_hmac(p0, c0, cs_pay0);
      close exists(false);
      leak exists(false);
    case none:
      assert [_]ill_formed_item_chars(hmac)(?cs_pay0);
      phmac = polarssl_hmac(p0, c0, cs_pay0);
      polarssl_cryptogram_constraints(cs_cg, phmac);
      close exists(true);
      leak exists(true);
  }
  close polarssl_pub(pub)(phmac);
  leak polarssl_pub(pub)(phmac);
  polarssl_public_generated_cryptogram_chars(polarssl_pub(pub), phmac);
  polarssl_public_generated_chars_assume(polarssl_pub(pub), cons('h', nil)); //Checked
  polarssl_public_generated_chars_join(
                                      polarssl_pub(pub), cons('h', nil), cs_cg);
}

lemma void serialize_symmetric_encrypted(int p0, int c0, 
                                         option<item> pay0, list<char> ent0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints_no_collision(?enc, ?cs, pub) &*&
           enc == symmetric_encrypted_item(p0, c0, pay0, ent0) &*& [_]pub(enc);
  ensures  proof_obligations(pub) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
{
  open [_]item_constraints_no_collision(enc, cs, pub);
  list<char> ent0_1 = take(GCM_ENT_SIZE, ent0);
  list<char> ent0_2 = drop(GCM_ENT_SIZE, ent0);
  assert ent0 == append(ent0_1, ent0_2);
  assert cs == cons('i', ?cs0);
  list<char> cs_cg = drop(GCM_ENT_SIZE, cs0);
  assert cs0 == append(ent0_1, cs_cg);
  assert [_]symmetric_encryption_entropy(enc)(?mac0, ?iv0);
  assert ent0_2 == cons(length(mac0), append(mac0, iv0));
  
  polarssl_cryptogram penc;
  switch(pay0)
  {
    case some(pay1):
      assert [_]well_formed_item_chars(enc)(?cs_pay0);
      assert [_]item_constraints_no_collision(pay1, cs_pay0, pub);
      penc = polarssl_auth_encrypted(p0, c0, mac0, cs_pay0, iv0);
      close exists(ent0);
      leak exists(ent0);
      close exists(false);
      leak exists(false);
    case none:
      assert [_]ill_formed_item_chars(enc)(?cs_pay0);
      penc = polarssl_auth_encrypted(p0, c0, mac0, cs_pay0, iv0);
      polarssl_cryptogram_constraints(cs_cg, penc);
      close exists(true);
      leak exists(true);
  }
  close polarssl_pub(pub)(penc);
  leak polarssl_pub(pub)(penc);
  polarssl_public_generated_cryptogram_chars(polarssl_pub(pub), penc);
  polarssl_public_generated_chars_assume(polarssl_pub(pub), cons('i', ent0_1)); //Checked
  polarssl_public_generated_chars_join(
                                  polarssl_pub(pub), cons('i', ent0_1), cs_cg);
}

lemma void serialize_asymmetric_encrypted(int p0, int c0, 
                                          option<item> pay0, list<char> ent0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints_no_collision(?enc, ?cs, pub) &*&
           enc == asymmetric_encrypted_item(p0, c0, pay0, ent0) &*& [_]pub(enc);
  ensures  proof_obligations(pub) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
{
  open [_]item_constraints_no_collision(enc, cs, pub);
  assert cs == cons('j', ?cs_cg);
  
  polarssl_cryptogram penc;
  switch(pay0)
  {
    case some(pay1):
      assert [_]well_formed_item_chars(enc)(?cs_pay0);
      assert [_]item_constraints_no_collision(pay1, cs_pay0, pub);
      penc = polarssl_asym_encrypted(p0, c0, cs_pay0, ent0);
      close exists(ent0);
      leak exists(ent0);
      close exists(false);
      leak exists(false);
    case none:
      assert [_]ill_formed_item_chars(enc)(?cs_pay0);
      penc = polarssl_asym_encrypted(p0, c0, cs_pay0, ent0);
      polarssl_cryptogram_constraints(cs_cg, penc);
      close exists(true);
      leak exists(true);
  }
  close polarssl_pub(pub)(penc);
  leak polarssl_pub(pub)(penc);
  polarssl_public_generated_cryptogram_chars(polarssl_pub(pub), penc);
  polarssl_public_generated_chars_assume(polarssl_pub(pub), cons('j', nil)); //Checked
  polarssl_public_generated_chars_join(
                                      polarssl_pub(pub), cons('j', nil), cs_cg);
}

lemma void serialize_asymmetric_signature(int p0, int c0, 
                                          option<item> pay0, list<char> ent0)
  requires proof_obligations(?pub) &*&
           [_]item_constraints_no_collision(?sig, ?cs, pub) &*&
           sig == asymmetric_signature_item(p0, c0, pay0, ent0) &*& [_]pub(sig);
  ensures  proof_obligations(pub) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
{
  open [_]item_constraints_no_collision(sig, cs, pub);
  assert cs == cons('k', ?cs_cg);
  
  polarssl_cryptogram psig;
  switch(pay0)
  {
    case some(pay1):
      assert [_]well_formed_item_chars(sig)(?cs_pay0);
      assert [_]item_constraints_no_collision(pay1, cs_pay0, pub);
      psig = polarssl_asym_signature(p0, c0, cs_pay0, ent0);
      close exists(ent0);
      leak exists(ent0);
      close exists(false);
      leak exists(false);
    case none:
      assert [_]ill_formed_item_chars(sig)(?cs_pay0);
      psig = polarssl_asym_signature(p0, c0, cs_pay0, ent0);
      polarssl_cryptogram_constraints(cs_cg, psig);
      close exists(true);
      leak exists(true);
  }
  close polarssl_pub(pub)(psig);
  leak polarssl_pub(pub)(psig);
  polarssl_public_generated_cryptogram_chars(polarssl_pub(pub), psig);
  polarssl_public_generated_chars_assume(polarssl_pub(pub), cons('k', nil)); //Checked
  polarssl_public_generated_chars_join(
                                      polarssl_pub(pub), cons('k', nil), cs_cg);
}

lemma void serialize_item(item i)
  requires proof_obligations(?pub) &*&
           [_]item_constraints_no_collision(i, ?cs, pub) &*&
           [_]pub(i);
  ensures  proof_obligations(pub) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
{
  switch (i)
  {
    case data_item(d0):
      serialize_data(d0);
    case pair_item(first0, second0):
      open [_]item_constraints_no_collision(i, cs, pub);
      assert [_]item_constraints_no_collision(first0, ?f_cs, pub);
      assert [_]item_constraints_no_collision(second0, ?s_cs, pub);
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
  requires [?f]world(?pub);
  ensures  [f]world(pub) &*& proof_obligations(pub); 
{
  open  [f]world(pub);
  open  [f]proof_obligations(pub);
  
  duplicate_lemma_function_pointer_chunk(public_collision);
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
  close [f]world(pub);
}

@*/

int serialize_to_public_message(char** dest, struct item* item)
  /*@ requires [?f0]world(?pub) &*& 
               [?f1]item(item, ?i, pub) &*& pointer(dest, _) &*& 
               [_]pub(i); @*/
  /*@ ensures  [f0]world(pub) &*& 
               [f1]item(item, i, pub) &*& pointer(dest, ?d) &*& 
               malloc_block(d, result) &*& result > 1 &*&
               polarssl_public_message(polarssl_pub(pub))
                                      (d, result, ?cs) &*&
               [_]item_constraints(_, i, cs, pub); @*/
{
  int size;
  char* temp;
  
  //@ open [f1]item(item, i, pub);
  //@ assert [f1]item->content |-> ?cont;
  //@ assert [f1]chars(cont, _, ?cs);
  size = item->size;
  
  temp = malloc_wrapper(size);
  memcpy(temp, item->content, (unsigned int) size);
  *dest = temp;

  //@ open [f0]world(pub);
  //@ close [f0]world(pub);
  //@ retreive_proof_obligations();
  //@ open [_]item_constraints(?b, i, cs, pub);
  //@ if (!b) serialize_item(i);
  //@ leak proof_obligations(pub);
  /*@ close polarssl_public_message(polarssl_pub(pub))
                                   (temp, size, cs); @*/
  //@ close [f1]item(item, i, pub);
  
  return size;
}
