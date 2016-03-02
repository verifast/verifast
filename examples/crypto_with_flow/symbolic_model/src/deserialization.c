#include "deserialization.h"

#include <string.h>

#include "principal_ids.h"
//@ #include "list.gh"
#include "serialization.h"

/*@

#define DESERIALIZE_ITEM_PROOF_CG(TAG, CG) \
  cryptogram cg = chars_for_cg_sur(cs_cg, TAG); \
  list<cryptogram> cgs_cg = cgs_in_chars(cs_cg); \
  close exists(cg); \
  assert cg == CG; \
  public_generated_extract(polarssl_pub(pub), cs_cg, cg); \
  open [_]polarssl_pub(pub)(cg); \

#define DESERIALIZE_ITEM_PROOF_PAY(IPAY, INOPAY, PROOF, ATTACK_EXTRA) \
  open [_]exists<bool>(?attack); \
  if (attack) \
  { \
    if (well_formed(cs_pay, nat_length(cs_pay))) \
    { \
      close proof_obligations(pub); \
      well_formed_upper_bound(cs_pay, nat_length(cs_pay), nat_of_int(INT_MAX)); \
      forall_mem(cg, cgs_in_chars(cs), (cg_level_upper_bound)(level_bound)); \
      cg_level_pay(cg, level_bound0); \
      deserialize_item_(level_bound0, nat_of_int(INT_MAX), cs_pay, pub); \
      open [_]item_constraints(?pay, cs_pay, pub); \
      assert [_]pub(pay); \
      i = IPAY; \
      close well_formed_item_chars(i)(cs_pay); \
      leak well_formed_item_chars(i)(cs_pay); \
      open proof_obligations(pub); \
      PROOF \
    } \
    else \
    { \
      i = INOPAY; \
      PROOF \
      close ill_formed_item_chars(i)(cs_pay); \
      leak ill_formed_item_chars(i)(cs_pay); \
    } \
  } \
  else \
  { \
    assert [_]item_constraints(?pay, cs_pay, pub); \
    ATTACK_EXTRA \
    i = IPAY; \
    well_formed_item_constraints(pay, i); \
    assert [_]pub(i); \
  } \

#define DESERIALIZE_ITEM_PROOF \
switch(length_bound) \
{ \
  case succ(length_bound0): \
    list<char> cs_tag = take(TAG_LENGTH, cs); \
    list<char> cs_cont = drop(TAG_LENGTH, cs); \
    take_append(TAG_LENGTH, cs_tag, cs_cont); \
    drop_append(TAG_LENGTH, cs_tag, cs_cont); \
    assert cs == append(cs_tag, cs_cont); \
    assert cs_tag == full_tag(head(cs)); \
    length_equals_nat_length(cs); \
    \
    list<cryptogram> cgs = cgs_in_chars(cs); \
    well_formed_upper_bound(cs, length_bound, nat_length(cs)); \
    assert true == well_formed(cs, nat_length(cs)); \
    public_generated_split(polarssl_pub(pub), cs, TAG_LENGTH); \
    open [_]public_generated(polarssl_pub(pub))(cs_cont); \
    cgs_in_chars_upper_bound_split(cs, cgs, TAG_LENGTH); \
    \
    item i; \
    open proof_obligations(pub); \
    if (head(cs) == TAG_DATA) \
    { \
      i = data_item(cs_cont); \
      assert is_public_data(?proof, pub); \
      close exists(info_for_item); \
      proof(i); \
    } \
    else if (head(cs) == TAG_PAIR) \
    { \
      int length_f_cs; \
      list<char> p_cs, f_cs, s_cs; \
      if (INT_MIN <= head(cs_cont) && head(cs_cont) <= INT_MAX) \
      { \
        length_f_cs = int_of_chars(take(sizeof(int), cs_cont)); \
        p_cs = drop(TAG_LENGTH + sizeof(int), cs); \
        f_cs = take(length_f_cs, p_cs); \
        s_cs = drop(length_f_cs, p_cs); \
        \
        list<cryptogram> f_cgs = cgs_in_chars(f_cs); \
        list<cryptogram> s_cgs = cgs_in_chars(s_cs); \
        \
        drop_drop(sizeof(int), TAG_LENGTH, cs); \
        length_drop(TAG_LENGTH + sizeof(int), cs); \
        length_take(length_f_cs, p_cs); \
        length_drop(length_f_cs, p_cs); \
        \
        public_generated_split(polarssl_pub(pub), cs_cont, sizeof(int)); \
        cgs_in_chars_upper_bound_split(cs_cont, cgs, sizeof(int)); \
        public_generated_split(polarssl_pub(pub), p_cs, length_f_cs); \
        cgs_in_chars_upper_bound_split(p_cs, cgs, length_f_cs); \
        \
        open [_]public_generated(polarssl_pub(pub))(f_cs); \
        open [_]public_generated(polarssl_pub(pub))(s_cs); \
        \
        cgs_in_chars_upper_bound_subset(f_cs, cgs); \
        cgs_in_chars_upper_bound_subset(s_cs, cgs); \
        forall_subset(f_cgs, cgs, (cg_level_upper_bound) \
                                  (level_bound)); \
        forall_subset(s_cgs, cgs, (cg_level_upper_bound) \
                                  (level_bound)); \
      } \
      else \
      { \
        assert false; \
      } \
      close proof_obligations(pub); \
      \
      deserialize_item_(level_bound, length_bound0, f_cs, pub); \
      deserialize_item_(level_bound, length_bound0, s_cs, pub); \
      \
      assert [_]item_constraints(?f, f_cs, pub); \
      assert [_]item_constraints(?s, s_cs, pub); \
      assert [_]pub(f); \
      assert [_]pub(s); \
      \
      open proof_obligations(pub); \
      assert is_public_pair_compose(?proof, pub); \
      proof(f, s); \
      i = pair_item(f, s); \
      close ic_pair(i)(f_cs, s_cs); \
    } \
    else if (head(cs) == TAG_NONCE) \
    { \
      assert cs_cont == cons(?inc, ?cs_cg); \
      public_generated_split(polarssl_pub(pub), cs_cont, 1); \
      DESERIALIZE_ITEM_PROOF_CG(tag_nonce, cg_nonce(?p0, ?c0)) \
      i = nonce_item(p0, c0, inc); \
      item i0 = nonce_item(p0, c0, 0); \
      \
      assert [_]pub(i0); \
      assert is_public_incremented_nonce(?proof, pub); \
      proof(i0, i); \
    } \
    else if (head(cs) == TAG_HASH) \
    { \
      list<char> cs_cg = cs_cont; \
      DESERIALIZE_ITEM_PROOF_CG(tag_hash, cg_hash(?cs_pay)) \
      DESERIALIZE_ITEM_PROOF_PAY(hash_item(some(pay)), \
                                 hash_item(none), \
                                 assert is_public_hash(?proof, pub); \
                                 proof(i);,) \
    } \
    else if (head(cs) == TAG_SYMMETRIC_KEY) \
    { \
      list<char> cs_cg = cs_cont; \
      DESERIALIZE_ITEM_PROOF_CG(tag_symmetric_key, cg_symmetric_key(?p0, ?c0)) \
      i = symmetric_key_item(p0, c0); \
    } \
    else if (head(cs) == TAG_PUBLIC_KEY) \
    { \
      list<char> cs_cg = cs_cont; \
      DESERIALIZE_ITEM_PROOF_CG(tag_public_key, cg_public_key(?p0, ?c0)) \
      i = public_key_item(p0, c0); \
    } \
    else if (head(cs) == TAG_PRIVATE_KEY) \
    { \
      list<char> cs_cg = cs_cont; \
      DESERIALIZE_ITEM_PROOF_CG(tag_private_key, cg_private_key(?p0, ?c0)) \
      i = private_key_item(p0, c0); \
    } \
    else if (head(cs) == TAG_HMAC) \
    { \
      list<char> cs_cg = cs_cont; \
      DESERIALIZE_ITEM_PROOF_CG(tag_hmac, cg_hmac(?p0, ?c0, ?cs_pay)) \
      DESERIALIZE_ITEM_PROOF_PAY(hmac_item(p0, c0, some(pay)), \
                                 hmac_item(p0, c0, none), \
                                 assert is_public_hmac(?proof, pub); \
                                 proof(i);,) \
    } \
    else if (head(cs) == TAG_SYMMETRIC_ENC) \
    { \
      list<char> ent1 = take(GCM_IV_SIZE, cs_cont); \
      list<char> cs_cg = drop(GCM_IV_SIZE, cs_cont); \
      take_append(GCM_IV_SIZE, ent1, cs_cg); \
      drop_append(GCM_IV_SIZE, ent1, cs_cg); \
      public_generated_split(polarssl_pub(pub), cs_cont, GCM_IV_SIZE); \
      cgs_in_chars_upper_bound_split(cs_cont, cgs, GCM_IV_SIZE); \
      \
      DESERIALIZE_ITEM_PROOF_CG(tag_auth_encrypted, \
                                cg_auth_encrypted(?p0, ?c0, ?cs_pay, ?iv0)) \
      list<char> ent2 = append(ent1, iv0); \
      take_append(GCM_IV_SIZE, ent1, iv0); \
      drop_append(GCM_IV_SIZE, ent1, iv0); \
      DESERIALIZE_ITEM_PROOF_PAY(symmetric_encrypted_item(p0, c0, some(pay), ent2), \
                                 symmetric_encrypted_item(p0, c0, none, ent2), \
                                 \
                                 assert is_public_symmetric_encrypted(?proof, pub); \
                                 proof(i);, \
                                 \
                                 assert [_]exists<list<char> >(?ent); \
                                 item i_orig = symmetric_encrypted_item(p0, c0, some(pay), ent); \
                                 assert [_]pub(i_orig); \
                                 assert is_public_symmetric_encrypted_entropy(?proof, pub); \
                                 i = symmetric_encrypted_item(p0, c0, some(pay), ent2); \
                                 proof(i_orig, ent2); \
                               ) \
      close ic_sym_enc(i)(iv0, cs_cg); \
    } \
    else if (head(cs) == TAG_ASYMMETRIC_ENC) \
    { \
      list<char> cs_cg = cs_cont; \
      DESERIALIZE_ITEM_PROOF_CG(tag_asym_encrypted, cg_asym_encrypted(?p0, ?c0, ?cs_pay, ?ent0)) \
      DESERIALIZE_ITEM_PROOF_PAY(asymmetric_encrypted_item(p0, c0, some(pay), ent0), \
                                 asymmetric_encrypted_item(p0, c0, none, ent0), \
                                 assert is_public_asymmetric_encrypted(?proof, pub); \
                                 proof(i);,) \
    } \
    else if (head(cs) == TAG_ASYMMETRIC_SIG) \
    { \
      list<char> cs_cg = cs_cont; \
      DESERIALIZE_ITEM_PROOF_CG(tag_asym_signature, cg_asym_signature(?p0, ?c0, ?cs_pay, ?ent0)) \
      DESERIALIZE_ITEM_PROOF_PAY(asymmetric_signature_item(p0, c0, some(pay), ent0), \
                                 asymmetric_signature_item(p0, c0, none, ent0), \
                                 \
                                 assert is_public_asymmetric_signature(?proof, pub); \
                                 proof(i);,) \
    } \
    else \
    { \
      assert false; \
    } \
    close ic_parts(i)(cs_tag, cs_cont); \
    close item_constraints(i, cs, pub); \
    leak item_constraints(i, cs, pub); \
    close proof_obligations(pub); \
  case zero: \
    assert false; \
}

lemma void deserialize_item_(nat level_bound, nat length_bound,
                             list<char> cs, predicate(item) pub)
  requires proof_obligations(pub) &*&
           //knowledge about first inductive paramter
           true == forall(cgs_in_chars(cs), (cg_level_upper_bound)(level_bound)) &*&
           //knowledge about second inductive paramter
           length(cs) <= int_of_nat(length_bound) &*&
           int_of_nat(length_bound) <= INT_MAX &*&
           true == well_formed(cs, length_bound) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
  ensures  proof_obligations(pub) &*&
           [_]item_constraints(?i, cs, pub) &*& [_]pub(i);
{
  // Dummy switch to enforce lexicographic induction
  switch(level_bound)
  {
    case succ(level_bound0):
      DESERIALIZE_ITEM_PROOF
    case zero:
      DESERIALIZE_ITEM_PROOF
  }
}

lemma void deserialize_item(list<char> cs, predicate(item) pub)
requires proof_obligations(pub) &*&
           length(cs) <= INT_MAX &*&
           true == well_formed(cs, nat_length(cs)) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
  ensures  proof_obligations(pub) &*&
           [_]item_constraints(?i, cs, pub) &*& [_]pub(i);
{
  well_formed_upper_bound(cs, nat_length(cs), nat_of_int(INT_MAX));
  open [_]public_generated(polarssl_pub(pub))(cs);
  cg_level_max_forall(cgs_in_chars(cs));
  deserialize_item_(cg_level_max(), nat_of_int(INT_MAX), cs, pub);
}

lemma void well_formed_pair_item(list<char> cs,
                                 list<char> cs_f, list<char> cs_s)
  requires length(cs) > TAG_LENGTH + 1 &*& length(cs) <= INT_MAX &*&
           head(cs) == TAG_PAIR &*&
           0 < length(cs_f) &*& length(cs_f) < INT_MAX &*&
           take(TAG_LENGTH, cs) == full_tag(TAG_PAIR) &*&
           drop(TAG_LENGTH, cs) == append(chars_of_int(length(cs_f)),
                                          append(cs_f, cs_s)) &*&
           true == well_formed(cs_f, nat_length(cs_f)) &*&
           true == well_formed(cs_s, nat_length(cs_s));
  ensures  true == well_formed(cs, nat_length(cs));
{
  length_equals_nat_length(cs);
  switch(nat_length(cs))
  {
    case succ(n):
      assert head(cs) == TAG_PAIR &*& length(cs) > TAG_LENGTH + 1;
      assert valid_tag(head(cs)) && take(TAG_LENGTH, cs) == full_tag(head(cs));
      list<char> cs_tag = take(TAG_LENGTH, cs);
      list<char> cs_cont = drop(TAG_LENGTH, cs);
      drop_append(TAG_LENGTH, cs_tag, cs_cont);

      well_formed_upper_bound(cs_f, nat_length(cs_f), n);
      well_formed_upper_bound(cs_s, nat_length(cs_s), n);
      take_append(length(cs_f), cs_f, cs_s);
      drop_append(length(cs_f), cs_f, cs_s);

      if (INT_MIN <= length(cs_f) && length(cs_f) <= INT_MAX)
      {
        take_append(sizeof(int), chars_of_int(length(cs_f)),
                                  append(cs_f, cs_s));
        drop_append(sizeof(int), chars_of_int(length(cs_f)),
                                  append(cs_f, cs_s));
        chars_of_unbounded_int_bounds(length(cs_f));
        head_append(chars_of_int(length(cs_f)), append(cs_f, cs_s));
        assert head(cs_cont) == head(chars_of_int(length(cs_f)));
        assert INT_MIN <= head(cs_cont) &*& INT_MAX >= head(cs_cont);
        assert take(sizeof(int), cs_cont) == chars_of_int(length(cs_f));
        int_of_chars_of_int(length(cs_f));
        assert length(cs_f) == int_of_chars(chars_of_int(length(cs_f)));
        assert length(cs) > TAG_LENGTH + sizeof(int) + length(cs_f);
        assert true == well_formed(cs_f, n);
        assert true == well_formed(cs_s, n);
        drop_drop(sizeof(int), TAG_LENGTH, cs);
      }
      else
      {
        assert false;
      }
    case zero:
      assert false;
  }
}

@*/

void parse_pair_item(char* message, int size)
  /*@ requires [?f1]world(?pub, ?key_clsfy) &*& exists(?cs_tag) &*&
               cs_tag == full_tag(TAG_PAIR) &*& TAG_LENGTH == length(cs_tag) &*&
               size <= INT_MAX - TAG_LENGTH &*& head(cs_tag) == TAG_PAIR &*&
               [?f2]crypto_chars(?kind, message, size, ?cs_cont) &*&
               switch(kind)
               {
                 case normal:
                   return true;
                 case secret:
                   return [_]item_constraints(pair_item(_, _),
                                              append(cs_tag, cs_cont), pub);
               }; @*/
  /*@ ensures  [f1]world(pub, key_clsfy) &*&
               [f2]crypto_chars(kind, message, size, cs_cont) &*&
               true == well_formed(append(cs_tag, cs_cont),
                                   nat_length(append(cs_tag, cs_cont))); @*/
{
  //@ open [f1]world(pub, key_clsfy);
  //@ close [f1]world(pub, key_clsfy);
  if (size <= (int) sizeof(int))
    abort_crypto_lib("Incorrect size for pair item");
  //@ list<char> cs = append(cs_tag, cs_cont);
  //@ take_append(TAG_LENGTH, cs_tag, cs_cont);
  //@ drop_append(TAG_LENGTH, cs_tag, cs_cont);

  //@ crypto_chars_limits(message);
  //@ crypto_chars_split(message, sizeof(int));
  //@ assert [f2]crypto_chars(kind, message, sizeof(int), ?size_f_cs);
  /*@ assert [f2]crypto_chars(kind, message + sizeof(int),
                              size - sizeof(int), ?cs_p); @*/
  //@ take_append(sizeof(int), size_f_cs, cs_p);
  //@ drop_append(sizeof(int), size_f_cs, cs_p);
  //@ assert cs_cont == append(size_f_cs, cs_p);
  //@ if (kind == normal) crypto_chars_to_chars(message, sizeof(int));
  /*@ if (kind == secret)
      {
        open [_]item_constraints(?p, cs, pub);
        assert [_]ic_parts(p)(?cs_tag0, ?cs_cont0);
        take_append(TAG_LENGTH, cs_tag0, cs_cont0);
        drop_append(TAG_LENGTH, cs_tag0, cs_cont0);
        public_crypto_chars(message, sizeof(int));
        assert [_]ic_pair(p)(?cs_f0, ?cs_s0);
        take_append(length(cs_f0), cs_f0, cs_s0);
        drop_append(length(cs_f0), cs_f0, cs_s0);
        assert cs_p == append(cs_f0, cs_s0);
      }
  @*/
  //@ chars_to_integer(message);
  int size_f = *((int*) ((void*) message));
  //@ assert size_f == int_of_chars(size_f_cs);
  //@ integer_to_chars(message);
  if (size_f < MINIMAL_STRING_SIZE || size_f > size - (int) sizeof(int))
    abort_crypto_lib("Incorrect size for pair item");
  int size_s = size - (int) sizeof(int) - size_f;
  //@ crypto_chars_limits(message + sizeof(int));
  //@ crypto_chars_split(message + sizeof(int), size_f);
  /*@ assert [f2]crypto_chars(kind, message + (int) sizeof(int),
                              size_f, ?cs_f); @*/
  /*@ assert [f2]crypto_chars(kind, message + (int) sizeof(int) + size_f,
                              size_s, ?cs_s); @*/
  //@ take_append(size_f, cs_f, cs_s);
  //@ drop_append(size_f, cs_f, cs_s);
  //@ assert cs_p == append(cs_f, cs_s);
  if (size_f <= TAG_LENGTH || size_s <= TAG_LENGTH)
    abort_crypto_lib("Incorrect size for pair item");
  /*@ assert cs_cont == append(chars_of_unbounded_int(length(cs_f)),
                               append(cs_f, cs_s)); @*/
  parse_item(message + (int) sizeof(int), size_f);
  parse_item(message + (int) sizeof(int) + size_f, size_s);
  //@ crypto_chars_join(message + sizeof(int));
  //@ if (kind == normal) chars_to_crypto_chars(message, sizeof(int));
  //@ if (kind == secret) chars_to_secret_crypto_chars(message, sizeof(int));
  //@ crypto_chars_join(message);

  //@ length_equals_nat_length(cs);
  //@ length_equals_nat_length(cs_cont);
  /*@ switch(nat_length(cs))
      {
        case succ(n):
          well_formed_upper_bound(cs_f, nat_length(cs_f), nat_length(cs_cont));
          well_formed_upper_bound(cs_s, nat_length(cs_s), nat_length(cs_cont));
          assert length(cs) > 0;
          assert length(cs) <= INT_MAX;
          assert true == well_formed(cs_f, nat_length(cs_f));
          assert true == well_formed(cs_s, nat_length(cs_s));
          head_append(cs_tag, cs_cont);
          well_formed_pair_item(cs, cs_f, cs_s);
        case zero:
          assert false;
      }
  @*/
}

void parse_item(char* buffer, int size)
  /*@ requires [?f1]world(?pub, ?key_clsfy) &*&
               [?f2]crypto_chars(?kind, buffer, size, ?cs) &*&
               size > TAG_LENGTH &*&
               kind == normal ? true :
                 [_]item_constraints(?i, cs, pub); @*/
  /*@ ensures  [f1]world(pub, key_clsfy) &*&
               [f2]crypto_chars(kind, buffer, size, cs) &*&
               true == well_formed(cs, nat_length(cs)); @*/
{
  //@ open [f1]world(pub, key_clsfy);
  //@ close [f1]world(pub, key_clsfy);
  //@ crypto_chars_limits(buffer);
  //@ crypto_chars_split(buffer, TAG_LENGTH);
  //@ assert [f2]crypto_chars(kind, buffer, TAG_LENGTH, ?cs_tag);
  /*@ assert [f2]crypto_chars(kind, buffer + TAG_LENGTH,
                              size - TAG_LENGTH,  ?cs_cont); @*/
  /*@ switch (kind)
      {
        case normal:
          crypto_chars_to_chars(buffer, TAG_LENGTH);
        case secret:
          open [_]item_constraints(_, cs, pub);
          public_crypto_chars(buffer, TAG_LENGTH);
      }
  @*/
  //@ open [f2]chars(buffer, TAG_LENGTH, cs_tag);
  char t = *(buffer);
  //@ close [f2]chars(buffer, TAG_LENGTH, cs_tag);
  check_tag(buffer, t);
  //@ assert cs_tag == full_tag(t);
  //@ length_equals_nat_length(cs);
  switch (t)
  {
    case TAG_DATA:
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case TAG_PAIR:
      //@ close exists(cs_tag);
      parse_pair_item(buffer + TAG_LENGTH, size - TAG_LENGTH);
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case TAG_NONCE:
      if (size != TAG_LENGTH + 1 + NONCE_SIZE)
        abort_crypto_lib("Could not parse nonce: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case TAG_HASH:
      if (size != TAG_LENGTH + HASH_SIZE)
        abort_crypto_lib("Could not parse hash: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case TAG_SYMMETRIC_KEY:
      if (size != TAG_LENGTH + GCM_KEY_SIZE)
        abort_crypto_lib("Could not parse symmetric key: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case TAG_PUBLIC_KEY:
      if (size != TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE)
        abort_crypto_lib("Could not parse public key: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case TAG_PRIVATE_KEY:
      if (size != TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE)
        abort_crypto_lib("Could not parse private key: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case TAG_HMAC:
      if (size != TAG_LENGTH + HMAC_SIZE)
        abort_crypto_lib("Could not parse private key: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case TAG_SYMMETRIC_ENC:
      if (size < TAG_LENGTH + GCM_IV_SIZE)
        abort_crypto_lib("Could not parse symmetric encrypted item: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case TAG_ASYMMETRIC_ENC:
      if (size > TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE)
        abort_crypto_lib("Could not parse asymmetric encrypted item: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case TAG_ASYMMETRIC_SIG:
      if (size > TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE)
        abort_crypto_lib("Could not parse asymmetric signature item: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    default:
      abort_crypto_lib("Found illegal tag during deserialization");
  }
  //@ if (kind == normal) chars_to_crypto_chars(buffer, TAG_LENGTH);
  //@ if (kind == secret) chars_to_secret_crypto_chars(buffer, TAG_LENGTH);
  //@ crypto_chars_join(buffer);
}

struct item* deserialize(char* buffer, int size)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               [?f1]chars(buffer, size, ?cs); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               [f1]chars(buffer, size, cs) &*&
               item(result, ?i, pub) &*& [_]pub(i); @*/
{
  if (size <= MINIMAL_STRING_SIZE)
    abort_crypto_lib("Found corrupted item during deserialization");

  struct item* item = malloc(sizeof(struct item));
  if (item == 0){abort_crypto_lib("malloc of item failed");}

  //@ open [f0]world(pub, key_clsfy);
  //@ public_chars(buffer, size);
  //@ close [f0]world(pub, key_clsfy);
  item->size = size;
  item->content = malloc_wrapper(item->size);
  //@ assert item->content |-> ?cont;
  //@ chars_to_crypto_chars(buffer, size);
  memcpy(item->content, buffer, (unsigned int) size);
  parse_item(buffer, size);
  //@ retreive_proof_obligations();
  //@ deserialize_item(cs, pub);
  //@ leak proof_obligations(pub);
  //@ assert [_]item_constraints(?i, cs, pub) &*& [_]pub(i);
  //@ chars_to_secret_crypto_chars(cont, size);
  //@ close item(item, i, pub);
  return item;
}
