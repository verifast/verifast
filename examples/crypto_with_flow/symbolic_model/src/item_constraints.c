#include "item_constraints.h"

/*@

lemma void well_formed_upper_bound(list<char> cs, nat upper_bound1,
                                                  nat upper_bound2)
  requires true == well_formed(cs, upper_bound1) &*&
           length(cs) <= int_of_nat(upper_bound2);
  ensures  true == well_formed(cs, upper_bound2);
{
  switch(upper_bound1)
  {
    case zero: assert false;
    case succ(n_ub1):
      switch(upper_bound2)
      {
        case zero: assert false;
        case succ(n_ub2):
          if (head(cs) == TAG_PAIR)
          {
            list<char> cs_tag     = take(TAG_LENGTH, cs);
            list<char> cs_content = drop(TAG_LENGTH, cs);
            assert cs == append(cs_tag, cs_content);
            assert cs_tag == full_tag(TAG_PAIR);
            assert length(cs) > TAG_LENGTH + 1;

            int length_f_cs, length_s_cs;
            list<char> p_cs, f_cs, s_cs;
            if (INT_MIN <= head(cs_content) &&
                INT_MAX >= head(cs_content))
            {
              length_f_cs = int_of_chars(take(sizeof(int), cs_content));
              length_s_cs = length(cs) - TAG_LENGTH - sizeof(int) - length_f_cs;
              p_cs = drop(sizeof(int), cs_content);
              length_drop(sizeof(int), cs_content);
              drop_drop(sizeof(int), TAG_LENGTH, cs);
              f_cs = take(length_f_cs, p_cs);
              s_cs = drop(length_f_cs, p_cs);
              assert length(cs) > TAG_LENGTH + sizeof(int) + length_f_cs;
              append_drop_take(p_cs, length_f_cs);
              assert p_cs == append(f_cs, s_cs);
              append_drop_take(cs_content, sizeof(int));
              assert cs_content == append(chars_of_int(length_f_cs), p_cs);
            }
            else
            {
              length_f_cs = head(cs_content);
              length_s_cs = length(cs) - TAG_LENGTH - 1 - length_f_cs;
              p_cs = drop(1, cs_content);
              f_cs = take(length_f_cs, p_cs);
              s_cs = drop(length_f_cs, p_cs);
              append_drop_take(p_cs, length_f_cs);
              assert p_cs == append(f_cs, s_cs);
              take_1(cs_content);
              append_drop_take(cs_content, 1);
              assert cs_content == cons(length_f_cs, p_cs);
              drop_drop(1, TAG_LENGTH, cs);
              assert p_cs == drop(TAG_LENGTH + 1, cs);
            }

            assert true == well_formed(f_cs, n_ub1);
            assert true == well_formed(s_cs, n_ub1);

            well_formed_upper_bound(f_cs, n_ub1, n_ub2);
            well_formed_upper_bound(s_cs, n_ub1, n_ub2);

            assert true == well_formed(f_cs, n_ub2);
            assert true == well_formed(s_cs, n_ub2);
            assert true == well_formed(cs, upper_bound2);
          }
      }
  }
}

lemma void well_formed_valid_tag(list<char> cs, nat len)
  requires true == well_formed(cs, len);
  ensures  valid_tag(head(cs)) &&
           take(TAG_LENGTH, cs) == full_tag(head(cs));
{
  switch(len) {case succ(n): case zero:}
}

lemma void well_formed_item_constraints(item i1, item i2)
  requires [_]item_constraints(i1, ?cs, ?pub);
  ensures  [_]well_formed_item_chars(i2)(cs);
{
  open  [_]item_constraints(i1, cs, pub);
  close well_formed_item_chars(i2)(cs);
  leak well_formed_item_chars(i2)(cs);
}

#define ITEM_CONSTRAINTS_DETERMINISTIC \
  switch(pay0) \
  { \
    case some(pay1): \
      if (!col) \
      { \
        open   [_]item_constraints(i, cs1, pub); \
        assert [_]ic_cg(i)(_, ?cg1); \
        assert [_]item_constraints(pay1, ?cs_pay1, pub); \
        open   [_]item_constraints(i, cs2, pub); \
        assert [_]ic_cg(i)(_, ?cg2); \
        assert [_]item_constraints(pay1, ?cs_pay2, pub); \
        item_constraints_deterministic(cs_pay1, cs_pay2, pay1); \
        assert cs_pay1 == cs_pay2; \
        chars_for_cg_inj(cg1, cg2); \
      } \
    case none: \
      assert false; \
  }

lemma void item_constraints_deterministic(list<char> cs1, list<char> cs2, item i)
  requires true == well_formed_item(i) &*&
           [_]item_constraints(i, cs1, ?pub) &*&
           [_]item_constraints(i, cs2, pub);
  ensures  col || cs1 == cs2;
{
  switch(i)
  {
    case data_item(d0):
      open [_]item_constraints(i, cs1, pub);
      open [_]item_constraints(i, cs2, pub);
    case pair_item(f0, s0):
      if (!col)
      {
        open [_]item_constraints(i, cs1, pub);
        open [_]ic_parts(i)(?cs_tag, ?cs_cont1);
        assert [_]item_constraints(f0, ?cs_f1, pub);
        assert [_]item_constraints(s0, ?cs_s1, pub);
        open [_]item_constraints(i, cs2, pub);
        open [_]ic_parts(i)(cs_tag, ?cs_cont2);
        assert [_]item_constraints(f0, ?cs_f2, pub);
        assert [_]item_constraints(s0, ?cs_s2, pub);
        item_constraints_deterministic(cs_f1, cs_f2, f0);
        item_constraints_deterministic(cs_s1, cs_s2, s0);
        assert cs1 == append(cs_tag, cs_cont1);
        assert cs2 == append(cs_tag, cs_cont2);
        append_drop_take(cs_cont1, sizeof(int));
        append_drop_take(cs_cont2, sizeof(int));
      }
    case nonce_item(p0, c0, inc0):
      open [_]item_constraints(i, cs1, pub);
      open [_]item_constraints(i, cs2, pub);
    case hash_item(pay0):
      ITEM_CONSTRAINTS_DETERMINISTIC;
    case symmetric_key_item(p0, c0):
      open [_]item_constraints(i, cs1, pub);
      open [_]item_constraints(i, cs2, pub);
    case public_key_item(p0, c0):
      open [_]item_constraints(i, cs1, pub);
      open [_]item_constraints(i, cs2, pub);
    case private_key_item(p0, c0):
      open [_]item_constraints(i, cs1, pub);
      open [_]item_constraints(i, cs2, pub);
    case hmac_item(p0, c0, pay0):
      ITEM_CONSTRAINTS_DETERMINISTIC;
    case symmetric_encrypted_item(p0, c0, pay0, ent0):
      switch(pay0)
      {
        case some(pay):
          if (!col)
          {
            open [_]item_constraints(i, cs1, pub);
            open [_]ic_parts(i)(?tag_cs, ?cont1);
            open [_]ic_sym_enc(i)(?iv1, ?cg_cs1);
            open [_]ic_cg(i)(_, ?cg1);
            assert [_]item_constraints(pay, ?cs_pay1, pub);
            open [_]item_constraints(i, cs2, pub);
            open [_]ic_parts(i)(tag_cs, ?cont2);
            open [_]ic_sym_enc(i)(?iv2, ?cg_cs2);
            open [_]ic_cg(i)(_, ?cg2);
            assert [_]item_constraints(pay, ?cs_pay2, pub);
            assert drop(GCM_IV_SIZE, ent0) == iv1;
            assert drop(GCM_IV_SIZE, ent0) == iv2;
            assert iv1 == iv2;
            assert cs1 == append(tag_cs, cont1);
            assert cs2 == append(tag_cs, cont2);
            append_take_drop_n(cont1, GCM_IV_SIZE);
            append_take_drop_n(cont2, GCM_IV_SIZE);
            item_constraints_deterministic(cs_pay1, cs_pay2, pay);
            assert cs_pay1 == cs_pay2;
            assert cg_cs1 == chars_for_cg(cg1);
            assert cg_cs2 == chars_for_cg(cg2);
            chars_for_cg_inj(cg1, cg2);
          }
        case none:
          assert false;
      }
    case asymmetric_encrypted_item(p0, c0, pay0, ent0):
      ITEM_CONSTRAINTS_DETERMINISTIC;
    case asymmetric_signature_item(p0, c0, pay0, ent0):
      ITEM_CONSTRAINTS_DETERMINISTIC;
  }
}

#define ITEM_CONSTRAINTS_INJECTIVE(TAG, BODY) \
  open [_]item_constraints(i1, cs, pub); \
  assert [_]ic_parts(i1)(?cs_tag1, ?cs1); \
  assert cs == append(cs_tag1, cs1); \
  open [_]item_constraints(i2, cs, pub); \
  assert [_]ic_parts(i2)(?cs_tag2, ?cs2); \
  assert cs == append(cs_tag2, cs2); \
  assert cs_tag1 == cs_tag2; \
  drop_append(TAG_LENGTH, cs_tag1, cs1); \
  drop_append(TAG_LENGTH, cs_tag2, cs2); \
  assert cs1 == cs2; \
  switch (i2) \
  { \
    case data_item(d2): \
      if (TAG == TAG_DATA) {if (!col) {BODY}} else {assert false;} \
    case pair_item(f2, s2): \
      if (TAG == TAG_PAIR) {if (!col) {BODY}} else {assert false;} \
    case nonce_item(p2, c2, inc2): \
      if (TAG == TAG_NONCE) {if (!col) {BODY}} else {assert false;} \
    case hash_item(pay2): \
      if (TAG == TAG_HASH) {if (!col) {BODY}} else {assert false;} \
    case symmetric_key_item(p2, c2): \
      if (TAG == TAG_SYMMETRIC_KEY) {if (!col) {BODY}} else {assert false;} \
    case public_key_item(p2, c2): \
      if (TAG == TAG_PUBLIC_KEY) {if (!col) {BODY}} else {assert false;} \
    case private_key_item(p2, c2): \
      if (TAG == TAG_PRIVATE_KEY) {if (!col) {BODY}} else {assert false;} \
    case hmac_item(p2, c2, pay2): \
      if (TAG == TAG_HMAC) {if (!col) {BODY}} else {assert false;} \
    case symmetric_encrypted_item(p2, c2, pay2, ent2): \
      if (TAG == TAG_SYMMETRIC_ENC) {if (!col) {BODY}} else {assert false;} \
    case asymmetric_encrypted_item(p2, c2, pay2, ent2): \
      if (TAG == TAG_ASYMMETRIC_ENC) {if (!col) {BODY}} else {assert false;} \
    case asymmetric_signature_item(p2, c2, pay2, ent2): \
      if (TAG == TAG_ASYMMETRIC_SIG) {if (!col) {BODY}} else {assert false;} \
  }

#define ITEM_CONSTRAINTS_INJECTIVE_PAYLOAD(BODY) \
  switch(pay1) \
  { \
    case some(pay1_): \
      open [_]well_formed_item_chars(i1)(?cs_pay1); \
      switch(pay2) \
      { \
        case some(pay2_): \
          open [_]well_formed_item_chars(i2)(?cs_pay2); \
          BODY assert cs_pay1 == cs_pay2; \
          item_constraints_injective(pay1_, pay2_, cs_pay1); \
          assert i1 == i2; \
        case none: \
          open [_]ill_formed_item_chars(i2)(?cs_pay2); \
          BODY assert false; \
      } \
    case none: \
      open [_]ill_formed_item_chars(i1)(?cs_pay1); \
      switch(pay2) \
      { \
        case some(pay2_): \
          open [_]well_formed_item_chars(i2)(?cs_pay2); \
          BODY assert false; \
        case none: \
          open [_]ill_formed_item_chars(i2)(?cs_pay2); \
          BODY assert i1 == i2; \
      } \
  } \

//Parser does not accept deeper nested macro in this proof
fixpoint int tag_symmetric_enc() { return TAG_SYMMETRIC_ENC; }
#define ITEM_CONSTRAINTS_SYM_ENC(REST) \
  assert i1 == symmetric_encrypted_item(p1, c1, pay1, ent1); \
  assert i2 == symmetric_encrypted_item(p2, c2, pay2, ent2); \
  assert [_]ic_sym_enc(i1)(?iv1, ?cs_cg1); \
  assert [_]ic_sym_enc(i2)(?iv2, ?cs_cg2); \
  assert iv1 == drop(gcm_iv_size, ent1); \
  assert iv2 == drop(gcm_iv_size, ent2); \
  list<char> cs_iv1 = take(gcm_iv_size, ent1); \
  list<char> cs_iv2 = take(gcm_iv_size, ent2); \
  assert cs_iv1 == cs_iv1; \
  drop_append(gcm_iv_size, cs_iv1, iv1); \
  drop_append(gcm_iv_size, cs_iv2, iv2); \
  REST;

lemma void item_constraints_injective(item i1, item i2, list<char> cs)
  requires [_]item_constraints(i1, cs, ?pub) &*&
           [_]item_constraints(i2, cs, pub);
  ensures  col || i1 == i2;
{
  switch (i1)
  {
    case data_item(d1):
      ITEM_CONSTRAINTS_INJECTIVE(TAG_DATA,
        assert i1 == i2;
      )
    case pair_item(f1, s1):
      ITEM_CONSTRAINTS_INJECTIVE(TAG_PAIR,
        assert [_]item_constraints(f1, ?cs_f1, pub);
        assert [_]item_constraints(s1, ?cs_s1, pub);
        assert [_]item_constraints(f2, ?cs_f2, pub);
        assert [_]item_constraints(s2, ?cs_s2, pub);
        int length_f1 = length(cs_f1);
        int length_s1 = length(cs_s1);
        int length_f2 = length(cs_f2);
        int length_s2 = length(cs_s2);
        list<char> length_cs_f1 = chars_of_unbounded_int(length_f1);
        list<char> length_cs_f2 = chars_of_unbounded_int(length_f2);

        drop_append(length(length_cs_f1), length_cs_f1, append(cs_f1, cs_s1));
        drop_append(length(length_cs_f2), length_cs_f2, append(cs_f2, cs_s2));
        take_append(length(length_cs_f1), length_cs_f1, append(cs_f1, cs_s1));
        take_append(length(length_cs_f2), length_cs_f2, append(cs_f2, cs_s2));
        drop_append(length_f1, cs_f1, cs_s1);
        drop_append(length_f2, cs_f2, cs_s2);
        take_append(length_f1, cs_f1, cs_s1);
        take_append(length_f2, cs_f2, cs_s2);

        if (length_f1 == length_f2)
        {
          item_constraints_injective(f1, f2, cs_f1);
          item_constraints_injective(s1, s2, cs_s1);
        }
        else
        {
          chars_of_unbounded_int_bounds(length_f1);
          chars_of_unbounded_int_bounds(length_f2);
          assert length(length_cs_f1) > 0;
          assert length(length_cs_f2) > 0;
          head_append(length_cs_f1, append(cs_f1, cs_s1));
          head_append(length_cs_f2, append(cs_f2, cs_s2));
          assert head(length_cs_f1) == head(length_cs_f1);
          assert length_f1 != length_f2;
          if (length(length_cs_f1) == sizeof(int))
          {
            if (length(length_cs_f2) == sizeof(int))
            {
              assert chars_of_int(length_f1) == chars_of_int(length_f2);
              chars_of_int_injective(length_f1, length_f2);
            }
          }
        }
      )
    case nonce_item(p1, c1, inc1):
      ITEM_CONSTRAINTS_INJECTIVE(TAG_NONCE,
        cryptogram cg1 = cg_nonce(p1, c1);
        cryptogram cg2 = cg_nonce(p2, c2);
        chars_for_cg_inj(cg1, cg2);
        assert i1 == i2;
      )
    case hash_item(pay1):
      ITEM_CONSTRAINTS_INJECTIVE(TAG_HASH,
        ITEM_CONSTRAINTS_INJECTIVE_PAYLOAD(
          cryptogram cg1 = cg_hash(cs_pay1);
          cryptogram cg2 = cg_hash(cs_pay2);
          chars_for_cg_inj(cg1, cg2);
        )
      )
    case symmetric_key_item(p1, c1):
      ITEM_CONSTRAINTS_INJECTIVE(TAG_SYMMETRIC_KEY,
        cryptogram cg1 = cg_symmetric_key(p1, c1);
        cryptogram cg2 = cg_symmetric_key(p2, c2);
        chars_for_cg_inj(cg1, cg2);
        assert i1 == i2;
      )
    case public_key_item(p1, c1):
      ITEM_CONSTRAINTS_INJECTIVE(TAG_PUBLIC_KEY,
        cryptogram cg1 = cg_public_key(p1, c1);
        cryptogram cg2 = cg_public_key(p2, c2);
        chars_for_cg_inj(cg1, cg2);
        assert i1 == i2;
      )
    case private_key_item(p1, c1):
      ITEM_CONSTRAINTS_INJECTIVE(TAG_PRIVATE_KEY,
        cryptogram cg1 = cg_private_key(p1, c1);
        cryptogram cg2 = cg_private_key(p2, c2);
        chars_for_cg_inj(cg1, cg2);
        assert i1 == i2;
      )
    case hmac_item(p1, c1, pay1):
      ITEM_CONSTRAINTS_INJECTIVE(TAG_HMAC,
        ITEM_CONSTRAINTS_INJECTIVE_PAYLOAD(
          cryptogram cg1 = cg_hmac(p1, c1, cs_pay1);
          cryptogram cg2 = cg_hmac(p2, c2, cs_pay2);
          chars_for_cg_inj(cg1, cg2);
        )
      )
    case symmetric_encrypted_item(p1, c1, pay1, ent1):
      ITEM_CONSTRAINTS_INJECTIVE(TAG_SYMMETRIC_ENC,
        ITEM_CONSTRAINTS_INJECTIVE_PAYLOAD(
          ITEM_CONSTRAINTS_SYM_ENC(
            cryptogram cg1 = cg_auth_encrypted(p1, c1, cs_pay1, iv1);
            cryptogram cg2 = cg_auth_encrypted(p2, c2, cs_pay2, iv2);
            chars_for_cg_inj(cg1, cg2);
          )
        )
      )
    case asymmetric_encrypted_item(p1, c1, pay1, ent1):
      ITEM_CONSTRAINTS_INJECTIVE(TAG_ASYMMETRIC_ENC,
        ITEM_CONSTRAINTS_INJECTIVE_PAYLOAD(
          cryptogram cg1 = cg_asym_encrypted(p1, c1, cs_pay1, ent1);
          cryptogram cg2 = cg_asym_encrypted(p2, c2, cs_pay2, ent2);
          chars_for_cg_inj(cg1, cg2);
        )
      )
    case asymmetric_signature_item(p1, c1, pay1, ent1):
      ITEM_CONSTRAINTS_INJECTIVE(TAG_ASYMMETRIC_SIG,
        ITEM_CONSTRAINTS_INJECTIVE_PAYLOAD(
          cryptogram cg1 = cg_asym_signature(p1, c1, cs_pay1, ent1);
          cryptogram cg2 = cg_asym_signature(p2, c2, cs_pay2, ent2);
          chars_for_cg_inj(cg1, cg2);
        )
      )
  }
}

@*/

char item_tag(char* content, int size)
  /*@ requires [?f1]crypto_chars(secret, content, size, ?cs) &*&
               [_]item_constraints(?i, cs, ?pub) &*&
               [_]public_invar(polarssl_pub(pub)); @*/
  /*@ ensures  [f1]crypto_chars(secret, content, size, cs) &*&
               head(cs) == result &*&
               take(TAG_LENGTH, cs) == full_tag(result); @*/
{
  //@ open [_]item_constraints(i, cs, pub);
  //@ crypto_chars_split(content, TAG_LENGTH);
  //@ public_crypto_chars(content, TAG_LENGTH);
  //@ open [f1]chars(content, TAG_LENGTH, cons(?tag, ?rest));
  return *content;
  //@ close [f1]chars(content, TAG_LENGTH, cons(tag, rest));
  //@ chars_to_secret_crypto_chars(content, TAG_LENGTH);
  //@ crypto_chars_join(content);
}

void write_tag(char* buffer, char tag)
  //@ requires chars(buffer, TAG_LENGTH, _);
  /*@ ensures  chars(buffer, TAG_LENGTH, ?cs) &*&
               head(cs) == tag &*& cs == full_tag(tag); @*/
{
  int offset = 0;
  while (offset < TAG_LENGTH)
    /*@ requires offset <= TAG_LENGTH &*&
                 true == ((char *)0 <= buffer + offset) &*&
                 buffer + offset <= (char *)UINTPTR_MAX &*&
                 chars(buffer + offset, TAG_LENGTH - offset, ?cs0) &*&
                 offset != TAG_LENGTH || cs0 == nil; @*/
    /*@ ensures  chars(buffer + old_offset, TAG_LENGTH - old_offset, ?cs1) &*&
                 old_offset == TAG_LENGTH || head(cs1) == tag &*&
                 cs1 == repeat(tag, nat_of_int(TAG_LENGTH - old_offset)); @*/
  {
    //@ length_equals_nat_length(cs0);
    //@ chars_limits(buffer + offset);
    //@ open chars(buffer + offset, TAG_LENGTH - offset, _);
    *(buffer + offset) = tag;
    offset = offset + 1;
    //@ open chars(buffer + offset, TAG_LENGTH - offset, ?cs1);
    //@ close chars(buffer + offset, TAG_LENGTH - offset, cs1);
    //@ recursive_call();
  }
}

void check_tag(char* buffer, char tag)
  //@ requires [?f]chars(buffer, TAG_LENGTH, ?cs);
  /*@ ensures  [f]chars(buffer, TAG_LENGTH, cs) &*&
               head(cs) == tag &*& cs == full_tag(tag); @*/
{
  int offset = 0;
  while (offset < TAG_LENGTH)
    /*@ requires offset <= TAG_LENGTH &*&
                 true == ((char *)0 <= buffer + offset) &*&
                 buffer + offset <= (char *)UINTPTR_MAX &*&
                 [f]chars(buffer + offset, TAG_LENGTH - offset, ?cs0) &*&
                 offset >= 0 &*& offset <= TAG_LENGTH &*&
                 offset != TAG_LENGTH || cs0 == nil; @*/
    /*@ ensures  [f]chars(buffer + old_offset, TAG_LENGTH - old_offset, cs0) &*&
                 cs0 == repeat(tag, nat_of_int(TAG_LENGTH - old_offset)) &*&
                 offset == TAG_LENGTH; @*/
  {
    //@ length_equals_nat_length(cs);
    //@ length_equals_nat_length(cs0);
    //@ chars_limits(buffer + offset);
    //@ open [f]chars(buffer + offset, TAG_LENGTH - offset, cs0);
    if (tag != *(buffer + offset))
      abort_crypto_lib("Checking tag failed");
    offset = offset + 1;
    //@ open [f]chars(buffer + offset, TAG_LENGTH - offset, ?cs1);
    //@ close [f]chars(buffer + offset, TAG_LENGTH - offset, cs1);
    //@ recursive_call();
  }
  //@ assert [f]chars(buffer, TAG_LENGTH, full_tag(tag));
  //@ length_equals_nat_length(full_tag(tag));
  //@ assert full_tag(tag) == cons(tag, _);
}

void check_tag2(char* buffer, char tag)
  /*@ requires [_]public_invar(?pub) &*&
               [_]decryption_key_classifier(?key_classifier) &*&
               network_permission(?p) &*&
               [?f2]crypto_chars(normal, buffer, TAG_LENGTH, ?cs) &*&
               check_tag2_ghost_args(?sym, ?garbage, ?p_key, ?c_key, ?rest_cs) &*&
               garbage ?
                 decryption_garbage(sym, p, ?s, p_key, c_key, append(cs, rest_cs)) &*&
                 s == known_value(0, full_tag(tag))
               :
                 true; @*/
  /*@ ensures  network_permission(p) &*&
               [f2]crypto_chars(normal, buffer, TAG_LENGTH, cs) &*&
               head(cs) == tag &*& cs == full_tag(tag) &*&
               garbage ?
                 decryption_permission(p) &*&
                 key_classifier(p_key, c_key, sym) ? true : col
               :
                 true; @*/
{
  //@ open check_tag2_ghost_args(sym, garbage, p_key, c_key, rest_cs);
  char tb[TAG_LENGTH];
  write_tag(tb, tag);
  //@ public_chars(tb, TAG_LENGTH);
  //@ chars_to_crypto_chars(tb, TAG_LENGTH);
  //@ assert crypto_chars(normal, tb, TAG_LENGTH, full_tag(tag));
  if (memcmp(buffer, tb, TAG_LENGTH) != 0)
    abort_crypto_lib("Checking tag failed");
  ///@ drop_append(TAG_LENGTH, full_tag(tag), drop(TAG_LENGTH, cs));
  ///@ head_append(full_tag(tag), drop(TAG_LENGTH, cs));
  //@ assert [f2]crypto_chars(?kind2, buffer, TAG_LENGTH, cs);
  /*@ if (garbage)
      {
        assert decryption_garbage(sym, p, ?s, p_key, c_key, _);
        close exists(pair(nil, rest_cs));
        close has_structure(append(cs, rest_cs), s);
        leak has_structure(append(cs, rest_cs), s);
        decryption_garbage(buffer, TAG_LENGTH, s);
      }
  @*/
}

void item_check_equal_(char* cont1, int size1, char* cont2, int size2)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal, ?count) &*&
               [?f1]crypto_chars(secret, cont1, size1, ?cs1) &*&
                 [_]item_constraints(?i1, cs1, pub) &*&
               [?f2]crypto_chars(secret, cont2, size2, ?cs2) &*&             
                 [_]item_constraints(?i2, cs2, pub); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal, count) &*&
               [f1]crypto_chars(secret, cont1, size1, cs1) &*&
               [f2]crypto_chars(secret, cont2, size2, cs2) &*&
               cs1 == cs2; @*/
{
  //@ open principal(principal, count);
  //@ open [f]world(pub, key_clsfy);
  //@ open [_]item_constraints(i1, cs1, pub);
  //@ assert [_]ic_parts(i1)(?cs_tag1, ?cs_cont1);
  //@ open [_]item_constraints(i2, cs2, pub);
  //@ assert [_]ic_parts(i2)(?cs_tag2, ?cs_cont2);
  char tag1 = item_tag(cont1, size1);
  char tag2 = item_tag(cont2, size2);

  if (tag1 != tag2)
    abort_crypto_lib("Items were not equal (different tags)");
  if (size1 != size2)
    abort_crypto_lib("Items were not equal (different size)");

  //@ crypto_chars_limits(cont1);
  //@ crypto_chars_limits(cont2);
  int size = size1 - TAG_LENGTH;
  char* b1 = cont1 + TAG_LENGTH;
  char* b2 = cont2 + TAG_LENGTH;
  //@ crypto_chars_split(cont1, TAG_LENGTH);
  //@ crypto_chars_split(cont2, TAG_LENGTH);
  //@ take_append(TAG_LENGTH, cs_tag1, cs_cont1);
  //@ drop_append(TAG_LENGTH, cs_tag1, cs_cont1);
  //@ take_append(TAG_LENGTH, cs_tag2, cs_cont2);
  //@ drop_append(TAG_LENGTH, cs_tag2, cs_cont2);
  //@ assert [f1]crypto_chars(secret, cont1, TAG_LENGTH, cs_tag1);
  //@ assert [f2]crypto_chars(secret, cont2, TAG_LENGTH, cs_tag2);
  //@ assert [f1]crypto_chars(secret, b1, size, cs_cont1);
  //@ assert [f2]crypto_chars(secret, b2, size, cs_cont2);
  //@ assert cs1 == append(cs_tag1, cs_cont1);
  //@ assert cs2 == append(cs_tag2, cs_cont2);
  //@ assert cs_tag1 == full_tag(tag1);
  //@ assert cs_tag2 == full_tag(tag2);

  if (tag1 == TAG_DATA)
  {
    //@ public_generated_split(polarssl_pub(pub), cs1, TAG_LENGTH);
    //@ public_generated_split(polarssl_pub(pub), cs2, TAG_LENGTH);
    //@ public_crypto_chars(b1, size);
    //@ chars_to_crypto_chars(b1, size);
    //@ public_crypto_chars(b2, size);
    //@ chars_to_crypto_chars(b2, size);
    if (memcmp(b1, b2, (unsigned int) size) != 0)
      abort_crypto_lib("Data items were not equal");
    //@ chars_to_secret_crypto_chars(b1, size);
    //@ chars_to_secret_crypto_chars(b2, size);
  }
  else if (tag1 == TAG_PAIR)
  {
    //@ assert [_]ic_pair(i1)(?cs_f1, ?cs_s1);
    //@ assert [_]ic_pair(i2)(?cs_f2, ?cs_s2);
    //@ crypto_chars_split(b1, sizeof(int));
    //@ crypto_chars_split(b2, sizeof(int));
    //@ public_crypto_chars(b1, sizeof(int));
    //@ chars_to_crypto_chars(b1, sizeof(int));
    //@ public_crypto_chars(b2, sizeof(int));
    //@ chars_to_crypto_chars(b2, sizeof(int));
    //@ chars_to_integer(b1);
    //@ chars_to_integer(b2);
    int f_size1 = *((int*) (void*) b1);
    int f_size2 = *((int*) (void*) b2);
    if (f_size1 != f_size2)
      abort_crypto_lib("Pair items were not equal (different size)");
    int f_size = f_size1;
    int s_size = size - f_size - (int) sizeof(int);
    char* fst1 = b1 + (int) sizeof(int);
    char* fst2 = b2 + (int) sizeof(int);
    char* snd1 = fst1 + f_size;
    char* snd2 = fst2 + f_size;
    //@ chars_to_secret_crypto_chars(b1, sizeof(int));
    //@ chars_to_secret_crypto_chars(b2, sizeof(int));
    //@ crypto_chars_split(fst1, f_size);
    //@ crypto_chars_split(fst2, f_size);
    //@ assert [f1]crypto_chars(secret, b1, sizeof(int), chars_of_int(f_size));
    //@ assert [f2]crypto_chars(secret, b2, sizeof(int), chars_of_int(f_size));
    //@ drop_append(sizeof(int), chars_of_int(f_size), append(cs_f1, cs_s1));
    //@ drop_append(sizeof(int), chars_of_int(f_size), append(cs_f2, cs_s2));
    //@ take_append(f_size, cs_f1, cs_s1);
    //@ take_append(f_size, cs_f2, cs_s2);
    //@ drop_append(f_size, cs_f1, cs_s1);
    //@ drop_append(f_size, cs_f2, cs_s2);
    //@ assert [f1]crypto_chars(secret, fst1, f_size, cs_f1);
    //@ assert [f2]crypto_chars(secret, fst2, f_size, cs_f2);
    //@ assert [f1]crypto_chars(secret, snd1, s_size, cs_s1);
    //@ assert [f2]crypto_chars(secret, snd2, s_size, cs_s2);
    //@ close principal(principal, count);
    //@ close [f]world(pub, key_clsfy);
    item_check_equal_(b1 + (int) sizeof(int), f_size,
                      b2 + (int) sizeof(int), f_size);
    item_check_equal_(b1 + (int) sizeof(int) + f_size, s_size,
                      b2 + (int) sizeof(int) + f_size, s_size);
    //@ open principal(principal, count);
    //@ open [f]world(pub, key_clsfy);
    //@ crypto_chars_join(fst1);
    //@ crypto_chars_join(fst2);
    //@ crypto_chars_join(b1);
    //@ crypto_chars_join(b2);
  }
  else
  {
    char* b_cg1 = b1;
    char* b_cg2 = b2;
    int size_cg = size;
    //@ list<char> cs_cg1 = cs_cont1;
    //@ list<char> cs_cg2 = cs_cont2;
    //@ tag cg_tag;
    if (tag1 == TAG_NONCE)
    {
      //@ cg_tag = tag_nonce;
      //@ assert cs_cont1 == cons(_, ?cs_cg1_);
      //@ assert cs_cont2 == cons(_, ?cs_cg2_);
      //@ cs_cg1 = cs_cg1_;
      //@ cs_cg2 = cs_cg2_;
      b_cg1 = b1 + 1;
      b_cg2 = b2 + 1;
      size_cg = size - 1;
      //@ crypto_chars_split(b1, 1);
      //@ crypto_chars_split(b2, 1);
      //@ public_crypto_chars(b1, 1);
      //@ public_crypto_chars(b2, 1);
      //@ open [f1]chars(b1, 1, _);
      //@ open [f2]chars(b2, 1, _);
      if (*b1 != *b2)
        abort_crypto_lib("Items were not equal: nonces with different increment");
      //@ close [f1]chars(b1, 1, _);
      //@ close [f2]chars(b2, 1, _);
      //@ chars_to_secret_crypto_chars(b1, 1);
      //@ chars_to_secret_crypto_chars(b2, 1);
    }
    else if (tag1 == TAG_SYMMETRIC_ENC)
    {
      //@ cg_tag = tag_encrypted;
      //@ assert [_]ic_sym_enc(i1)(?iv1, ?cs_cg1_);
      //@ assert [_]ic_sym_enc(i2)(?iv2, ?cs_cg2_);
      //@ cs_cg1 = cs_cg1_;
      //@ cs_cg2 = cs_cg2_;
      //@ take_append(GCM_IV_SIZE, take(GCM_IV_SIZE, cs_cont1), drop(GCM_IV_SIZE, cs_cont1));
      //@ take_append(GCM_IV_SIZE, take(GCM_IV_SIZE, cs_cont2), drop(GCM_IV_SIZE, cs_cont2));
      //@ drop_append(GCM_IV_SIZE, take(GCM_IV_SIZE, cs_cont1), drop(GCM_IV_SIZE, cs_cont1));
      //@ drop_append(GCM_IV_SIZE, take(GCM_IV_SIZE, cs_cont2), drop(GCM_IV_SIZE, cs_cont2));
      b_cg1 = b1 + GCM_IV_SIZE;
      b_cg2 = b2 + GCM_IV_SIZE;
      size_cg = size - GCM_IV_SIZE;
      //@ crypto_chars_split(b1, GCM_IV_SIZE);
      //@ crypto_chars_split(b2, GCM_IV_SIZE);
      //@ public_crypto_chars(b1, GCM_IV_SIZE);
      //@ public_crypto_chars(b2, GCM_IV_SIZE);
      //@ chars_to_crypto_chars(b1, GCM_IV_SIZE);
      //@ chars_to_crypto_chars(b2, GCM_IV_SIZE);
      if (memcmp(b1, b2, GCM_IV_SIZE) != 0)
        abort_crypto_lib("Items were not equal: encrypted items with different iv's");
      //@ chars_to_secret_crypto_chars(b1, GCM_IV_SIZE);
      //@ chars_to_secret_crypto_chars(b2, GCM_IV_SIZE);
    }
    else if (tag1 != TAG_HASH && tag1 != TAG_SYMMETRIC_KEY && tag1 != TAG_PUBLIC_KEY &&
        tag1 != TAG_PRIVATE_KEY && tag1 != TAG_HMAC && 
        tag1 != TAG_ASYMMETRIC_ENC && tag1 != TAG_ASYMMETRIC_SIG)
    {
      abort_crypto_lib("Found illegal tag while checking item equality");
    }
    //@ if (tag1 == TAG_HASH)           cg_tag = tag_hash;
    //@ if (tag1 == TAG_SYMMETRIC_KEY)  cg_tag = tag_symmetric_key;
    //@ if (tag1 == TAG_PUBLIC_KEY)     cg_tag = tag_public_key;
    //@ if (tag1 == TAG_PRIVATE_KEY)    cg_tag = tag_private_key;
    //@ if (tag1 == TAG_HMAC)           cg_tag = tag_hmac;
    //@ if (tag1 == TAG_ASYMMETRIC_ENC) cg_tag = tag_asym_encrypted;
    //@ if (tag1 == TAG_ASYMMETRIC_SIG) cg_tag = tag_asym_signature;
    
    //@ cryptogram cg1;
    //@ cryptogram cg2;
    /*@ if (col)
       {
         cg1 = chars_for_cg_sur(cs_cg1, cg_tag);
         cg2 = chars_for_cg_sur(cs_cg2, cg_tag);
         crypto_chars_to_chars(b_cg1, size_cg);
         crypto_chars_to_chars(b_cg2, size_cg);
         public_chars_extract(b_cg1, cg1);
         public_chars_extract(b_cg2, cg2);
         chars_to_secret_crypto_chars(b_cg1, size_cg);
         chars_to_secret_crypto_chars(b_cg2, size_cg);
       }
       else
       {
         assert [_]ic_cg(i1)(cs_cg1, ?cg1_);
         assert [_]ic_cg(i2)(cs_cg2, ?cg2_);
         cg1 = cg1_;
         cg2 = cg2_;
       }
    @*/
    //@ close memcmp_ghost_args(b_cg1, cg1);
    //@ close memcmp_ghost_args(b_cg2, cg2);
    if (memcmp(b_cg1, b_cg2, (unsigned int) size_cg) != 0)
      abort_crypto_lib("Items were not equal");
    /*@ if (tag1 == TAG_NONCE || tag1 == TAG_SYMMETRIC_ENC)
        {
          crypto_chars_join(b1);
          crypto_chars_join(b2);
        }
    @*/
  }
  //@ assert cs1 == cs2;
  //@ crypto_chars_join(cont1);
  //@ crypto_chars_join(cont2);
  //@ close principal(principal, count);
  //@ close [f]world(pub, key_clsfy);
  return;
}

void item_check_equal(struct item* item1, struct item* item2)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal, ?count) &*&
               [?f1]item(item1, ?i1, pub) &*& [?f2]item(item2, ?i2, pub); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal, count) &*&
               [f1]item(item1, i1, pub) &*& [f2]item(item2, i2, pub) &*&
               col || i1 == i2; @*/
{
  debug_print("COMPARING ITEMS\n");
  //@ open [f1]item(item1, i1, pub);
  //@ open [f2]item(item2, i2, pub);
  item_check_equal_(item1->content, item1->size,
                    item2->content, item2->size);
  //@ assert [f1]crypto_chars(secret, _, _, ?cs);
  //@ item_constraints_injective(i1, i2, cs);
  //@ close [f1]item(item1, i1, pub);
  //@ close [f2]item(item2, i2, pub);
  return;
}
