#include "deserialization.h"

#include <string.h>
//@ #include <list.gh>

#include "principal_ids.h"
#include "serialization.h"

/*@

#define DESERIALIZE_ITEM_PROOF_CG(TAG, CG) \
  cryptogram cg = ccs_for_cg_sur(ccs_cg, TAG); \
  assert cg == CG; \
  public_ccs_cg(cg); \
  open [_]polarssl_pub(pub)(cg); \

#define DESERIALIZE_ITEM_PROOF_PAY(IPAY, INOPAY, PROOF, ATTACK_EXTRA) \
  open [_]exists<bool>(?attack); \
  if (attack || col) \
  { \
    forall_t_elim(forallcg, (cg_in_ccs_implies_level_below)(ccs, level_bound), cg); \
    assert true == cg_in_ccs_implies_level_below(ccs, level_bound, cg); \
    assert true == sublist(ccs_for_cg(cg), ccs); \
    assert col || cg_level_below(level_bound, cg); \
    if (!col && well_formed_ccs(forallc, forallcs, \
                                nat_length(ccs_pay), ccs_pay)) \
    { \
      close proof_obligations(pub); \
      well_formed_upper_bound(nat_length(ccs_pay), nat_of_int(INT_MAX), ccs_pay); \
      cg_level_ccs_pay(cg, level_bound0); \
      deserialize_item_(level_bound0, nat_of_int(INT_MAX), ccs_pay); \
      open [_]item_constraints(?pay, ccs_pay, pub); \
      assert [_]pub(pay); \
      i = IPAY; \
      close well_formed_item_ccs(i)(ccs_pay); \
      leak well_formed_item_ccs(i)(ccs_pay); \
      open proof_obligations(pub); \
      PROOF \
    } \
    else \
    { \
      i = INOPAY; \
      PROOF \
      if (!col) \
      { \
        close ill_formed_item_ccs(i)(ccs_pay); \
        leak ill_formed_item_ccs(i)(ccs_pay); \
      } \
    } \
  } \
  else \
  { \
    assert [_]item_constraints(?pay, ccs_pay, pub); \
    ATTACK_EXTRA \
    i = IPAY; \
    well_formed_item_constraints(pay, i); \
    assert [_]pub(i); \
  } \

#define DESERIALIZE_ITEM_PROOF \
  switch(length_bound) \
  { \
    case succ(length_bound0): \
      list<crypto_char> ccs_tag = take(TAG_LENGTH, ccs); \
      list<crypto_char> ccs_cont = drop(TAG_LENGTH, ccs); \
      take_append(TAG_LENGTH, ccs_tag, ccs_cont); \
      drop_append(TAG_LENGTH, ccs_tag, ccs_cont); \
      head_append(ccs_tag, ccs_cont); \
      length_equals_nat_length(ccs); \
      public_ccs_split(ccs, TAG_LENGTH); \
      assert ccs == append(ccs_tag, ccs_cont); \
      assert ccs_tag == full_ctag(head(ccs)); \
      assert [_]public_ccs(ccs_tag); \
      \
      char tag = not_forall_t(forallc, (notf)((valid_ctag)(head(ccs)))); \
      assert head(ccs) == c_to_cc(tag); \
      SWITCH_TAG(tag) \
      open proof_obligations(pub); \
      well_formed_upper_bound(length_bound, nat_length(ccs), ccs);  \
      assert true == well_formed_ccs(forallc, forallcs, nat_length(ccs), ccs); \
      \
      item i; \
      if (head(ccs) == c_to_cc(TAG_DATA)) \
      { \
        public_cs_to_ccs(ccs_cont); \
        list<char> data = \
          not_forall_t(forallcs, (notf)((cs_to_ccs_eq)(ccs_cont))); \
        i = data_item(data); \
        assert is_public_data(?proof, pub); \
        proof(i); \
      } \
      else if (head(ccs) == c_to_cc(TAG_PAIR)) \
      { \
        int length_f_ccs, length_s_ccs; \
        list<crypto_char> p_ccs, f_ccs, s_ccs; \
        fixpoint(list<crypto_char>, bool) wf = \
                (well_formed_ccs)(forallc, forallcs, length_bound0); \
        char c = not_forall_t(forallc, \
              (notf)((well_formed_pair)(forallcs, wf, ccs_cont))); \
        \
        if (INT_MIN <= c && c <= INT_MAX) \
        { \
          list<char> cs_flength = not_forall_t(forallcs, \
            (notf)((well_formed_pair_bounded)(wf, ccs_cont))); \
          length_f_ccs = int_of_chars(cs_flength); \
          length_s_ccs = length(ccs_cont) - sizeof(int) - length_f_ccs; \
          assert length(ccs_cont) > sizeof(int) + length_f_ccs; \
          p_ccs = drop(sizeof(int), ccs_cont); \
          length_drop(sizeof(int), ccs_cont); \
          drop_drop(sizeof(int), TAG_LENGTH, ccs); \
          f_ccs = take(length_f_ccs, p_ccs); \
          s_ccs = drop(length_f_ccs, p_ccs); \
          assert length(ccs_cont) > sizeof(int) + length_f_ccs; \
          append_drop_take(p_ccs, length_f_ccs); \
          assert p_ccs == append(f_ccs, s_ccs); \
          append_drop_take(ccs_cont, sizeof(int)); \
          public_ccs_split(ccs_cont, sizeof(int)); \
          public_ccs_split(p_ccs, length_f_ccs); \
          \
          append_assoc(ccs_tag, cs_to_ccs(cs_flength), p_ccs); \
          append_assoc(ccs_tag, cs_to_ccs(cs_flength), f_ccs); \
          append_assoc(cs_to_ccs(cs_flength), f_ccs, s_ccs); \
          append_assoc(ccs_tag, append(cs_to_ccs(cs_flength), f_ccs), s_ccs); \
          sublist_append(append(ccs_tag, cs_to_ccs(cs_flength)), f_ccs, s_ccs); \
          sublist_append(append(ccs_tag, append(cs_to_ccs(cs_flength), f_ccs)), s_ccs, nil); \
          cg_level_ccs_sublist(ccs, f_ccs, level_bound); \
          cg_level_ccs_sublist(ccs, s_ccs, level_bound); \
        } \
        else \
        { \
          assert false; \
        } \
        close proof_obligations(pub); \
        \
        deserialize_item_(level_bound, length_bound0, f_ccs); \
        deserialize_item_(level_bound, length_bound0, s_ccs); \
        \
        assert [_]item_constraints(?f, f_ccs, pub); \
        assert [_]item_constraints(?s, s_ccs, pub); \
        assert [_]pub(f); \
        assert [_]pub(s); \
        \
        open proof_obligations(pub); \
        assert is_public_pair_compose(?proof, pub); \
        proof(f, s); \
        i = pair_item(f, s); \
        close ic_pair(i)(f_ccs, s_ccs); \
      } \
      else if (head(ccs) == c_to_cc(TAG_NONCE)) \
      { \
        assert ccs_cont == cons(?cc_inc, ?ccs_cg); \
        public_ccs_split(ccs_cont, 1); \
        public_cs_to_ccs(cons(cc_inc, nil)); \
        list<char> cs_inc = \
          not_forall_t(forallcs, (notf)((cs_to_ccs_eq)(cons(cc_inc, nil)))); \
        assert cs_to_ccs(cs_inc) == cons(cc_inc, nil); \
        assert cs_inc == cons(?inc, _); \
        assert cc_inc == c_to_cc(inc); \
        DESERIALIZE_ITEM_PROOF_CG(tag_nonce, cg_nonce(?p0, ?c0)) \
        i = nonce_item(p0, c0, inc); \
        item i0 = nonce_item(p0, c0, 0); \
        assert [_]pub(i0); \
        assert is_public_incremented_nonce(?proof, pub); \
        proof(i0, i); \
        close ic_cg(i)(ccs_cg, cg); \
      } \
      else if (head(ccs) == c_to_cc(TAG_HASH)) \
      { \
        list<crypto_char> ccs_cg = ccs_cont; \
        sublist_append(ccs_tag, ccs_cont, nil); \
        assert true == sublist(ccs_cg, append(ccs_tag, append(ccs_cont, nil))); \
        assert true == sublist(ccs_cg, ccs); \
        DESERIALIZE_ITEM_PROOF_CG(tag_hash, cg_sha512_hash(?ccs_pay)) \
        DESERIALIZE_ITEM_PROOF_PAY(hash_item(some(pay)), \
                                   hash_item(none), \
                                   assert is_public_hash(?proof, pub); \
                                   proof(i);,) \
        close ic_cg(i)(ccs_cg, cg); \
      } \
      else if (head(ccs) == c_to_cc(TAG_SYMMETRIC_KEY)) \
      { \
        list<crypto_char> ccs_cg = ccs_cont; \
        DESERIALIZE_ITEM_PROOF_CG(tag_symmetric_key, cg_symmetric_key(?p0, ?c0)) \
        i = symmetric_key_item(p0, c0); \
        close ic_cg(i)(ccs_cg, cg); \
      } \
      else if (head(ccs) == c_to_cc(TAG_PUBLIC_KEY)) \
      { \
        list<crypto_char> ccs_cg = ccs_cont; \
        DESERIALIZE_ITEM_PROOF_CG(tag_public_key, cg_rsa_public_key(?p0, ?c0)) \
        i = public_key_item(p0, c0); \
        close ic_cg(i)(ccs_cg, cg); \
      } \
      else if (head(ccs) == c_to_cc(TAG_PRIVATE_KEY)) \
      { \
        list<crypto_char> ccs_cg = ccs_cont; \
        DESERIALIZE_ITEM_PROOF_CG(tag_private_key, cg_rsa_private_key(?p0, ?c0)) \
        i = private_key_item(p0, c0); \
        close ic_cg(i)(ccs_cg, cg); \
      } \
      else if (head(ccs) == c_to_cc(TAG_HMAC)) \
      { \
        list<crypto_char> ccs_cg = ccs_cont; \
        sublist_append(ccs_tag, ccs_cont, nil); \
        DESERIALIZE_ITEM_PROOF_CG(tag_hmac, cg_sha512_hmac(?p0, ?c0, ?ccs_pay)) \
        DESERIALIZE_ITEM_PROOF_PAY(hmac_item(p0, c0, some(pay)), \
                                   hmac_item(p0, c0, none), \
                                   assert is_public_hmac(?proof, pub); \
                                   proof(i);,) \
        close ic_cg(i)(ccs_cg, cg); \
      } \
      else if (head(ccs) == c_to_cc(TAG_SYMMETRIC_ENC)) \
      { \
        list<crypto_char> ent1 = take(GCM_IV_SIZE, ccs_cont); \
        list<crypto_char> ccs_cg = drop(GCM_IV_SIZE, ccs_cont); \
        append_assoc(ccs_tag, ent1, ccs_cg); \
        sublist_append(append(ccs_tag, ent1), ccs_cg, nil); \
        take_append(GCM_IV_SIZE, ent1, ccs_cg); \
        drop_append(GCM_IV_SIZE, ent1, ccs_cg); \
        public_ccs_split(ccs_cont, GCM_IV_SIZE); \
        \
        DESERIALIZE_ITEM_PROOF_CG(tag_auth_encrypted, \
                                  cg_aes_auth_encrypted(?p0, ?c0, ?ccs_pay, ?iv0)) \
        list<crypto_char> ent2 = append(ent1, iv0); \
        take_append(GCM_IV_SIZE, ent1, iv0); \
        drop_append(GCM_IV_SIZE, ent1, iv0); \
        DESERIALIZE_ITEM_PROOF_PAY( \
            symmetric_encrypted_item(p0, c0, some(pay), ent2), \
            symmetric_encrypted_item(p0, c0, none, ent2), \
            \
            assert is_public_symmetric_encrypted(?proof, pub); \
            proof(i);, \
            \
            assert [_]exists<list<crypto_char> >(?ent); \
            item i_orig = symmetric_encrypted_item(p0, c0, some(pay), ent); \
            assert [_]pub(i_orig); \
            assert is_public_symmetric_encrypted_entropy(?proof, pub); \
            i = symmetric_encrypted_item(p0, c0, some(pay), ent2); \
            proof(i_orig, ent2); \
        ) \
        close ic_sym_enc(i)(iv0, ccs_cg); \
        close ic_cg(i)(ccs_cg, cg); \
      } \
      else if (head(ccs) == c_to_cc(TAG_ASYMMETRIC_ENC)) \
      { \
        list<crypto_char> ccs_cg = ccs_cont; \
        sublist_append(ccs_tag, ccs_cont, nil); \
        DESERIALIZE_ITEM_PROOF_CG(tag_asym_encrypted, cg_rsa_encrypted(?p0, ?c0, ?ccs_pay, ?ent0)) \
        DESERIALIZE_ITEM_PROOF_PAY(asymmetric_encrypted_item(p0, c0, some(pay), ent0), \
                                  asymmetric_encrypted_item(p0, c0, none, ent0), \
                                  assert is_public_asymmetric_encrypted(?proof, pub); \
                                  proof(i);,) \
        close ic_cg(i)(ccs_cg, cg); \
      } \
      else if (head(ccs) == c_to_cc(TAG_ASYMMETRIC_SIG)) \
      { \
        list<crypto_char> ccs_cg = ccs_cont; \
        sublist_append(ccs_tag, ccs_cont, nil); \
        DESERIALIZE_ITEM_PROOF_CG(tag_asym_signature, cg_rsa_signature(?p0, ?c0, ?ccs_pay, ?ent0)) \
        DESERIALIZE_ITEM_PROOF_PAY(asymmetric_signature_item(p0, c0, some(pay), ent0), \
                                  asymmetric_signature_item(p0, c0, none, ent0), \
                                  assert is_public_asymmetric_signature(?proof, pub); \
                                  proof(i);,) \
        close ic_cg(i)(ccs_cg, cg); \
      } \
      else \
      { \
        assert false; \
      } \
      \
      close ic_parts(i)(ccs_tag, ccs_cont); \
      close item_constraints(i, ccs, pub); \
      leak item_constraints(i, ccs, pub); \
      close proof_obligations(pub); \
      return i; \
    case zero: \
      assert false; \
  } \

lemma item deserialize_item_(nat level_bound, nat length_bound,
                             list<crypto_char> ccs)
  requires FORALLP_C &*& FORALLP_CS &*&
           proof_obligations(?pub) &*& [_]public_invar(polarssl_pub(pub)) &*&
           //knowledge about first inductive paramter
           [_]is_forall_t<cryptogram>(?forallcg) &*&
           true == forallcg((cg_in_ccs_implies_level_below)(ccs, level_bound)) &*&
           //knowledge about second inductive paramter
           length(ccs) <= int_of_nat(length_bound) &*&
           int_of_nat(length_bound) <= INT_MAX &*&
           true == well_formed_ccs(forallc, forallcs, length_bound, ccs) &*&
           [_]public_ccs(ccs);
  ensures  proof_obligations(pub) &*&
           [_]item_constraints(result, ccs, pub) &*& [_]pub(result);
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

lemma item deserialize_item(list<crypto_char> ccs)
  requires FORALLP_C &*& FORALLP_CS &*&
           proof_obligations(?pub) &*& [_]public_invar(polarssl_pub(pub)) &*&
           length(ccs) <= INT_MAX &*&
           true == well_formed_ccs(forallc, forallcs, nat_length(ccs), ccs) &*&
           [_]public_ccs(ccs);
  ensures  proof_obligations(pub) &*&
           [_]item_constraints(result, ccs, pub) &*& [_]pub(result);
{
  well_formed_upper_bound(nat_length(ccs), nat_of_int(INT_MAX), ccs);
  cg_level_ccs_max(ccs);
  return deserialize_item_(cg_level_max(), nat_of_int(INT_MAX), ccs);
}

lemma void well_formed_pair_item(list<crypto_char> ccs,
                                 int length_ccs_f,
                                 list<crypto_char> ccs_f,
                                 list<crypto_char> ccs_s)
  requires FORALLP_C &*& FORALLP_CS &*&
           length(ccs) > TAG_LENGTH + 1 &*& length(ccs) <= INT_MAX &*&
           head(ccs) == c_to_cc(TAG_PAIR) &*&
           length_ccs_f == length(ccs_f) &*&
           0 < length_ccs_f &*& length_ccs_f < INT_MAX &*&
           take(TAG_LENGTH, ccs) == full_ctag(c_to_cc(TAG_PAIR)) &*&
           drop(TAG_LENGTH, ccs) == append(cs_to_ccs(chars_of_int(length_ccs_f)),
                                           append(ccs_f, ccs_s)) &*&
           true == well_formed_ccs(forallc, forallcs, nat_length(ccs_f), ccs_f) &*&
           true == well_formed_ccs(forallc, forallcs, nat_length(ccs_s), ccs_s);
  ensures  true == well_formed_ccs(forallc, forallcs, nat_length(ccs), ccs);
{
  length_equals_nat_length(ccs);
  list<crypto_char> ccs_tag = take(TAG_LENGTH, ccs);
  list<crypto_char> ccs_cont = drop(TAG_LENGTH, ccs);
  assert TAG_LENGTH == length(ccs_tag);
  take_append(TAG_LENGTH, ccs_tag, ccs_cont);
  drop_append(TAG_LENGTH, ccs_tag, ccs_cont);
  SWITCH_TAG(TAG_PAIR);
  switch(nat_length(ccs))
  {
    case succ(n):
      fixpoint(list<crypto_char>, bool) wf =
        (well_formed_ccs)(forallc, forallcs, n);
      assert head(ccs) == c_to_cc(TAG_PAIR) &*& length(ccs) > TAG_LENGTH + 1;
      assert length(ccs_tag) == TAG_LENGTH;
      head_append(ccs_tag, ccs_cont);
      if (!exists_t<char>(forallc, (valid_ctag)(head(ccs_tag))))
      {
        forall_t_elim(forallc, (notf)((valid_ctag)(head(ccs_tag))), TAG_PAIR);
        assert false;
      }
      assert true == valid_full_ctag(forallc, take(TAG_LENGTH, ccs));
      assert INT_MIN <= length_ccs_f && length_ccs_f <= INT_MAX;
      take_append(length(ccs_f), ccs_f, ccs_s);
      drop_append(length(ccs_f), ccs_f, ccs_s);
      chars_of_unbounded_int_bounds(length_ccs_f);
      cs_to_ccs_length(chars_of_int(length_ccs_f));
      take_append(sizeof(int), cs_to_ccs(chars_of_int(length_ccs_f)),
                  append(ccs_f, ccs_s));
      drop_append(sizeof(int), cs_to_ccs(chars_of_int(length_ccs_f)),
                  append(ccs_f, ccs_s));
      well_formed_upper_bound(nat_length(ccs_f), n, ccs_f);
      well_formed_upper_bound(nat_length(ccs_s), n, ccs_s);
      if (!exists_t<list<char> >(forallcs,
                  (well_formed_pair_bounded)(wf, ccs_cont)))
      {
        forall_t_elim(forallcs,
          (notf)((well_formed_pair_bounded)(wf, ccs_cont)),
          chars_of_int(length_ccs_f));
        assert false;
      }
      assert take(sizeof(int), ccs_cont) == cs_to_ccs(chars_of_int(length_ccs_f));
      char c = head(chars_of_unbounded_int(length_ccs_f));
      switch(chars_of_unbounded_int(length_ccs_f)){case nil: case cons(x00, xs00):}
      chars_of_unbounded_int_bounds(length_ccs_f);
      assert c_to_cc(c) == head(take(sizeof(int), ccs_cont));
      assert c_to_cc(c) == head(ccs_cont);
      assert INT_MIN <= c && INT_MAX >= c;
      if (!exists_t(forallc, (well_formed_pair)(forallcs, wf, ccs_cont)))
      {
        forall_t_elim(forallc,
          (notf)((well_formed_pair)(forallcs, wf, ccs_cont)), c);
        assert false;
      }
    case zero:
      assert false;
  }
}

@*/

void parse_pair_item(char* message, int size)
  /*@ requires FORALLP_C &*& FORALLP_CS &*&
               [?f1]world(?pub, ?key_clsfy) &*& exists(?ccs_tag) &*&
               ccs_tag == full_ctag(c_to_cc(TAG_PAIR)) &*&
               TAG_LENGTH == length(ccs_tag) &*&
               size <= INT_MAX - TAG_LENGTH &*& head(ccs_tag) == c_to_cc(TAG_PAIR) &*&
               [?f2]crypto_chars(?kind, message, size, ?ccs_cont) &*&
               switch(kind)
               {
                 case normal:
                   return true;
                 case secret:
                   return [_]item_constraints(pair_item(_, _),
                                              append(ccs_tag, ccs_cont), pub);
               }; @*/
  /*@ ensures  [f1]world(pub, key_clsfy) &*&
               [f2]crypto_chars(kind, message, size, ccs_cont) &*&
               true == well_formed_ccs(forallc, forallcs,
                                   nat_length(append(ccs_tag, ccs_cont)),
                                   append(ccs_tag, ccs_cont)); @*/
{
  //@ open [f1]world(pub, key_clsfy);
  //@ close [f1]world(pub, key_clsfy);
  if (size <= (int) sizeof(int))
    abort_crypto_lib("Incorrect size for pair item");
  //@ list<crypto_char> ccs = append(ccs_tag, ccs_cont);
  //@ take_append(TAG_LENGTH, ccs_tag, ccs_cont);
  //@ drop_append(TAG_LENGTH, ccs_tag, ccs_cont);
  //@ crypto_chars_limits(message);
  //@ crypto_chars_split(message, sizeof(int));
  //@ assert [f2]crypto_chars(kind, message, sizeof(int), ?size_f_ccs);
  /*@ assert [f2]crypto_chars(kind, message + sizeof(int),
                              size - sizeof(int), ?ccs_p); @*/
  //@ take_append(sizeof(int), size_f_ccs, ccs_p);
  //@ drop_append(sizeof(int), size_f_ccs, ccs_p);
  //@ assert ccs_cont == append(size_f_ccs, ccs_p);
  /*@ if (kind == secret)
      {
        assert [_]item_constraints(?p, ccs, pub);
        OPEN_ITEM_CONSTRAINTS(p, ccs, pub);
        public_crypto_chars(message, sizeof(int));
      }
      else
      {
        crypto_chars_to_chars(message, sizeof(int));
      }
  @*/
  //@ assert [f2]chars(message, sizeof(int), ?size_f_cs);
  //@ assert cs_to_ccs(size_f_cs) == size_f_ccs;
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
                              size_f, ?ccs_f); @*/
  /*@ assert [f2]crypto_chars(kind, message + (int) sizeof(int) + size_f,
                              size_s, ?ccs_s); @*/
  //@ take_append(size_f, ccs_f, ccs_s);
  //@ drop_append(size_f, ccs_f, ccs_s);
  //@ assert ccs_p == append(ccs_f, ccs_s);
  if (size_f <= TAG_LENGTH || size_s <= TAG_LENGTH)
    abort_crypto_lib("Incorrect size for pair item");
  /*@ assert ccs_cont == append(cs_to_ccs(chars_of_unbounded_int(length(ccs_f))),
                                append(ccs_f, ccs_s)); @*/
  /*@ if (kind == secret)
      {
        assert [_]item_constraints(?p, ccs, pub);
        OPEN_ITEM_CONSTRAINTS(p, ccs, pub);
        assert [_]ic_pair(p)(?ccs_f0, ?ccs_s0);
        assert [_]item_constraints(_, ccs_f0, pub);
        assert [_]item_constraints(_, ccs_s0, pub);
        cs_to_ccs_inj(chars_of_int(length(ccs_f)),
                      chars_of_int(length(ccs_f0)));
        take_append(size_f, ccs_f0, ccs_s0);
        drop_append(size_f, ccs_f0, ccs_s0);
      }
  @*/
  parse_item(message + (int) sizeof(int), size_f);
  parse_item(message + (int) sizeof(int) + size_f, size_s);

  //@ crypto_chars_join(message + sizeof(int));
  //@ if (kind == normal) chars_to_crypto_chars(message, sizeof(int));
  //@ if (kind == secret) chars_to_secret_crypto_chars(message, sizeof(int));
  //@ crypto_chars_join(message);

  //@ length_equals_nat_length(ccs);
  //@ length_equals_nat_length(ccs_cont);
  /*@ switch(nat_length(ccs))
      {
        case succ(n):
          well_formed_upper_bound(nat_length(ccs_f), nat_length(ccs_cont), ccs_f);
          well_formed_upper_bound(nat_length(ccs_s), nat_length(ccs_cont), ccs_s);
          assert length(ccs) > 0;
          assert length(ccs) <= INT_MAX;
          assert true == well_formed_ccs(forallc, forallcs, nat_length(ccs_f), ccs_f);
          assert true == well_formed_ccs(forallc, forallcs, nat_length(ccs_s), ccs_s);
          head_append(ccs_tag, ccs_cont);
          well_formed_pair_item(ccs, size_f, ccs_f, ccs_s);
        case zero:
          assert false;
      }
  @*/
}

void parse_item(char* buffer, int size)
  /*@ requires FORALLP_C &*& FORALLP_CS &*&
               [?f1]world(?pub, ?key_clsfy) &*&
               [?f2]crypto_chars(?kind, buffer, size, ?ccs) &*&
               size > TAG_LENGTH &*&
               kind == normal ? true :
                 [_]item_constraints(?i, ccs, pub); @*/
  /*@ ensures  [f1]world(pub, key_clsfy) &*&
               [f2]crypto_chars(kind, buffer, size, ccs) &*&
               true == well_formed_ccs(forallc, forallcs, nat_length(ccs), ccs); @*/
{
  //@ open [f1]world(pub, key_clsfy);
  //@ close [f1]world(pub, key_clsfy);
  //@ crypto_chars_limits(buffer);
  //@ crypto_chars_split(buffer, TAG_LENGTH);
  //@ assert [f2]crypto_chars(kind, buffer, TAG_LENGTH, ?ccs_tag);
  /*@ assert [f2]crypto_chars(kind, buffer + TAG_LENGTH,
                              size - TAG_LENGTH,  ?cs_cont); @*/
  /*@ switch (kind)
      {
        case normal:
          crypto_chars_to_chars(buffer, TAG_LENGTH);
        case secret:
          assert [_]item_constraints(?i, ccs, pub);
          OPEN_ITEM_CONSTRAINTS(i, ccs, pub);
          public_crypto_chars(buffer, TAG_LENGTH);
      }
  @*/
  //@ open [f2]chars(buffer, TAG_LENGTH, ?cs_tag);
  //@ assert ccs_tag == cs_to_ccs(cs_tag);
  char t = *(buffer);
  //@ close [f2]chars(buffer, TAG_LENGTH, cs_tag);
  check_tag(buffer, t);
  //@ cs_to_ccs_full_tag(t);
  //@ assert cs_tag == full_tag(t);
  //@ length_equals_nat_length(ccs);
  //@ SWITCH_TAG(t)
  switch (t)
  {
    case TAG_DATA:
      break;
    case TAG_PAIR:
      //@ close exists(ccs_tag);
      parse_pair_item(buffer + TAG_LENGTH, size - TAG_LENGTH);
      break;
    case TAG_NONCE:
      if (size != TAG_LENGTH + 1 + NONCE_SIZE)
        abort_crypto_lib("Could not parse nonce: illegal size");
      break;
    case TAG_HASH:
      if (size != TAG_LENGTH + HASH_SIZE)
        abort_crypto_lib("Could not parse hash: illegal size");
      break;
    case TAG_SYMMETRIC_KEY:
      if (size != TAG_LENGTH + GCM_KEY_SIZE)
        abort_crypto_lib("Could not parse symmetric key: illegal size");
      break;
    case TAG_PUBLIC_KEY:
      if (size != TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE)
        abort_crypto_lib("Could not parse public key: illegal size");
      break;
    case TAG_PRIVATE_KEY:
      if (size != TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE)
        abort_crypto_lib("Could not parse private key: illegal size");
      break;
    case TAG_HMAC:
      if (size != TAG_LENGTH + HMAC_SIZE)
        abort_crypto_lib("Could not parse private key: illegal size");
      break;
    case TAG_SYMMETRIC_ENC:
      if (size < TAG_LENGTH + GCM_IV_SIZE + MINIMAL_STRING_SIZE)
        abort_crypto_lib("Could not parse symmetric encrypted item: illegal size");
      break;
    case TAG_ASYMMETRIC_ENC:
      if (size > TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE ||
          size < TAG_LENGTH + MINIMAL_STRING_SIZE)
        abort_crypto_lib("Could not parse asymmetric encrypted item: illegal size");
      break;
    case TAG_ASYMMETRIC_SIG:
      if (size > TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE ||
          size < TAG_LENGTH + MINIMAL_STRING_SIZE)
        abort_crypto_lib("Could not parse asymmetric signature item: illegal size");
      break;
    default:
      abort_crypto_lib("Found illegal tag during deserialization");
  }
  /*@ if (!exists_t<char>(forallc, (valid_ctag)(head(ccs))))
      {
        forall_t_elim(forallc, (notf)((valid_ctag)(head(ccs))), t);
        assert false;
      }
  @*/
  //@ assert true == well_formed_ccs(forallc, forallcs, nat_length(ccs), ccs);
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
  //@ assert [f1]crypto_chars(normal, buffer, size, ?ccs);
  crypto_memcpy(item->content, buffer, (unsigned int) size);
  //@ get_forall_t<char>();
  //@ get_forall_t<list<char> >();
  parse_item(buffer, size);
  //@ retreive_proof_obligations();
  //@ deserialize_item(ccs);
  //@ leak proof_obligations(pub);
  //@ assert [_]item_constraints(?i, ccs, pub) &*& [_]pub(i);
  //@ cs_to_ccs_crypto_chars(cont, cs);
  //@ cs_to_ccs_crypto_chars(buffer, cs);
  //@ chars_to_secret_crypto_chars(cont, size);
  //@ close item(item, i, pub);
  return item;
}
