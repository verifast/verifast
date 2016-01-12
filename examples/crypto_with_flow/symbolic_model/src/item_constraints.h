#ifndef ITEM_CONSTRAINTS_H
#define ITEM_CONSTRAINTS_H

#include "item.h"
#include "invariants.h"

#define TAG_DATA            'a'
#define TAG_PAIR            'b'
#define TAG_NONCE           'c'
#define TAG_HASH            'd'
#define TAG_SYMMETRIC_KEY   'e'
#define TAG_PUBLIC_KEY      'f'
#define TAG_PRIVATE_KEY     'g'
#define TAG_HMAC            'h'
#define TAG_SYMMETRIC_ENC   'i'
#define TAG_ASYMMETRIC_ENC  'j'
#define TAG_ASYMMETRIC_SIG  'k'

# define TAG_LENGTH MINIMAL_STRING_SIZE

/*@

//Each item has the following serialized form:
//  ______________________
// | TAG | ACTUAL CONTENT |
// |_____|________________|
//
//  TAG
//    *unique for each kind of item
//    *repetition of same character for simpler proofs
//    *size(TAG) == TAG_LENGTH to easily support decryption
//  ACTUAL CONTENT
//    *depends on the kind of item

// e.g. full_tag('a') == cons('a', cons('a', cons('a', cons('a', ...))))
fixpoint list<char> full_tag(char tag)
{
  return repeat(tag, nat_of_int(TAG_LENGTH));
}

// e.g. full_tag_for_item(data_item(...)) == cons('a', cons('a', cons('a', ...)))
fixpoint list<char> full_tag_for_item(item i)
{
  return full_tag(tag_for_item(i));
}

#define WELL_FORMED(CS_TAG, CS_CONT, TAG) \
  { \
    head_append(CS_TAG, CS_CONT); \
    take_append(TAG_LENGTH, CS_TAG, CS_CONT); \
    drop_append(TAG_LENGTH, CS_TAG, CS_CONT); \
    assert length(append(CS_TAG, CS_CONT)) > TAG_LENGTH; \
    assert head(append(CS_TAG, CS_CONT)) == TAG; \
    assert true == valid_tag(head(append(CS_TAG, CS_CONT))); \
    assert take(TAG_LENGTH, append(CS_TAG, CS_CONT)) == full_tag(head(append(CS_TAG, CS_CONT))); \
    length_equals_nat_length(append(CS_TAG, CS_CONT)); \
    switch(nat_length(append(CS_TAG, CS_CONT))) {case succ(s0): case zero:} \
  }

fixpoint bool well_formed(list<char> cs, nat upper_bound)
{
  switch(upper_bound)
  {
    case succ(n):
      return
        //correct total length
        length(cs) > TAG_LENGTH &&
        //correct tag
        valid_tag(head(cs)) && take(TAG_LENGTH, cs) == full_tag(head(cs)) &&
        //correct data_item
        (
          head(cs) != TAG_DATA ||
          true
        ) &&
        //correct pair_item
        (
          head(cs) != TAG_PAIR ||
          (
            length(cs) > TAG_LENGTH + 1 &&
            (
              INT_MIN <= head(drop(TAG_LENGTH, cs)) &&
              INT_MAX >= head(drop(TAG_LENGTH, cs)) ?
              (
                //size of first part within C bounds
                int_of_chars(take(sizeof(int), drop(TAG_LENGTH, cs))) > 0 &&
                length(cs) > TAG_LENGTH + sizeof(int) +
                             int_of_chars(take(sizeof(int), drop(TAG_LENGTH, cs))) &&
                well_formed(take(int_of_chars(take(sizeof(int), drop(TAG_LENGTH, cs))),
                                 drop(TAG_LENGTH + sizeof(int), cs)), n) &&
                well_formed(drop(int_of_chars(take(sizeof(int), drop(TAG_LENGTH, cs))),
                                 drop(TAG_LENGTH + sizeof(int), cs)), n)
              )
              :
              (
                //size of first part NOT within C bounds
                //only 1 char reserved for size of first part
                head(drop(TAG_LENGTH, cs)) > 0 &&
                length(cs) > TAG_LENGTH + 1 + head(drop(TAG_LENGTH, cs)) &&
                well_formed(take(head(drop(TAG_LENGTH, cs)),
                                 drop(TAG_LENGTH + 1, cs)), n) &&
                well_formed(drop(head(drop(TAG_LENGTH, cs)),
                                 drop(TAG_LENGTH + 1, cs)), n)
              )
            )
          )
        ) &&
        //correct nonce_item
        (
          head(cs) != TAG_NONCE ||
          length(cs) == TAG_LENGTH + 1 + NONCE_SIZE
        ) &&
        //correct hash_item
        (
          head(cs) != TAG_HASH ||
          length(cs) == TAG_LENGTH + HASH_SIZE
        ) &&
        //correct symmetric_key_item
        (
          head(cs) != TAG_SYMMETRIC_KEY ||
          length(cs) == TAG_LENGTH + GCM_KEY_SIZE
        ) &&
        //correct public_key_item
        (
          head(cs) != TAG_PUBLIC_KEY ||
          length(cs) == TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE
        ) &&
        //correct private_key_item
        (
          head(cs) != TAG_PRIVATE_KEY ||
          length(cs) == TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE
        ) &&
        //correct hmac_item
        (
          head(cs) != TAG_HMAC ||
          length(cs) == TAG_LENGTH + HMAC_SIZE
        ) &&
        //correct symmetric_encrypted_item
        (
          head(cs) != TAG_SYMMETRIC_ENC ||
          length(cs) >= TAG_LENGTH + GCM_ENT_SIZE
        ) &&
        //correct asymmetric_encrypted_item
        (
          head(cs) != TAG_ASYMMETRIC_ENC ||
          length(cs) <= TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE
        ) &&
        //correct asymmetric_signed_item
        (
          head(cs) != TAG_ASYMMETRIC_SIG ||
          length(cs) <= TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE
        );
    case zero:
      return false;
  }
}

lemma void well_formed_upper_bound(list<char> cs, nat upper_bound1,
                                                  nat upper_bound2);
  requires true == well_formed(cs, upper_bound1) &*&
           length(cs) <= int_of_nat(upper_bound2);
  ensures  true == well_formed(cs, upper_bound2);

lemma void well_formed_valid_tag(list<char> cs, nat len);
  requires true == well_formed(cs, len);
  ensures  valid_tag(head(cs)) &&
           take(TAG_LENGTH, cs) == full_tag(head(cs));

predicate_ctor well_formed_item_chars(item i)(list<char> cs) =
  true == well_formed(cs, nat_length(cs))
;

predicate_ctor ill_formed_item_chars(item i)(list<char> cs) =
  false == well_formed(cs, nat_length(cs))
;

#define ITEM_CONSTRAINTS_PUBLIC \
  [_]public_generated(polarssl_pub(pub))(cs_content) &*& \
  [_]public_generated(polarssl_pub(pub))(cs)

#define ITEM_CONSTRAINTS_PUBLIC_IF_COLLISION \
  (col ? ITEM_CONSTRAINTS_PUBLIC : true)

#define ITEM_CONSTRAINTS_CG(CS, CG) \
  exists(?cg) &*& cg == CG &*& \
  col || (CS == chars_for_cg(cg) && cg_is_generated(cg))

#define ITEM_CONSTRAINTS_PAY(PAY, NONE) \
  col ? true : \
  switch(pay0) \
  { \
    case some(pay1): \
      return [_]well_formed_item_chars(i)(PAY) &*& \
            length(PAY) <= INT_MAX &*& \
            [_]item_constraints(pay1, PAY, pub); \
    case none: \
      return [_]ill_formed_item_chars(i)(PAY) &*& \
            length(PAY) <= INT_MAX &*& \
            col ? true : [_]public_generated(polarssl_pub(pub))(PAY) &*& NONE; \
  } \

predicate_ctor ic_parts(item i)(list<char> cs_tag, list<char> cs_cont) = true;
predicate_ctor ic_pair(item i)(list<char> cs_f, list<char> cs_s) = true;
predicate_ctor ic_sym_enc(item i)(list<char> mac, list<char> iv, list<char> cg_cs) = true;

predicate item_constraints(item i, list<char> cs, predicate(item) pub) =
  true == well_formed(cs, nat_length(cs)) &*& length(cs) <= INT_MAX &*&
  ic_parts(i)(?cs_tag, ?cs_content) &*& cs == append(cs_tag, cs_content) &*&
  length(cs_tag) == TAG_LENGTH &*& cs_tag == cons(?tag, _) &*&
  cs_tag == full_tag(tag) &*& tag == tag_for_item(i) &*&
  [_]public_generated(polarssl_pub(pub))(cs_tag) &*&
  ITEM_CONSTRAINTS_PUBLIC_IF_COLLISION &*&
  switch(i)
  {
    case data_item(cs1): return
      tag == TAG_DATA &*&
        cs_content == cs1 &*&
        ITEM_CONSTRAINTS_PUBLIC;
    case pair_item(f0, s0): return
      tag == TAG_PAIR &*&
        ic_pair(i)(?cs_f0, ?cs_s0) &*&
        [_]item_constraints(f0, cs_f0, pub) &*&
        [_]item_constraints(s0, cs_s0, pub) &*&
        length(cs_content) > sizeof(int) &*&
        take(sizeof(int), cs_content) == chars_of_unbounded_int(length(cs_f0)) &*&
        drop(sizeof(int), cs_content) == append(cs_f0, cs_s0) &*&
        [_]public_generated(polarssl_pub(pub))(take(sizeof(int), cs_content));
    case nonce_item(p0, c0, inc0): return
      tag == TAG_NONCE &*&
        cs_content == cons(inc0, ?cs_cg) &*&
        [_]public_generated(polarssl_pub(pub))(cons(inc0, nil)) &*&
        length(cs_cg) == NONCE_SIZE &*&
        ITEM_CONSTRAINTS_CG(cs_cg, cg_nonce(p0, c0));
    case hash_item(pay0): return
      tag == TAG_HASH &*&
        length(cs_content) == HASH_SIZE &*&
        ITEM_CONSTRAINTS_CG(cs_content, cg_hash(?cs_pay1)) &*&
        ITEM_CONSTRAINTS_PAY(cs_pay1, true);
    case symmetric_key_item(p0, c0): return
      tag == TAG_SYMMETRIC_KEY &*&
        length(cs_content) == GCM_KEY_SIZE &*&
        ITEM_CONSTRAINTS_CG(cs_content, cg_symmetric_key(p0, c0));
    case public_key_item(p0, c0): return
      tag == TAG_PUBLIC_KEY &*&
        length(cs_content) == RSA_SERIALIZED_KEY_SIZE &*&
        ITEM_CONSTRAINTS_CG(cs_content, cg_public_key(p0, c0));
    case private_key_item(p0, c0): return
      tag == TAG_PRIVATE_KEY &*&
        length(cs_content) == RSA_SERIALIZED_KEY_SIZE &*&
        ITEM_CONSTRAINTS_CG(cs_content, cg_private_key(p0, c0));
    case hmac_item(p0, c0, pay0): return
      tag == TAG_HMAC &*&
        ITEM_CONSTRAINTS_CG(cs_content, cg_hmac(p0, c0, ?cs_pay1)) &*&
        ITEM_CONSTRAINTS_PAY(cs_pay1, [_]pub(symmetric_key_item(p0, c0)));
    case symmetric_encrypted_item(p0, c0, pay0, ent0): return
      tag == TAG_SYMMETRIC_ENC &*&
        ic_sym_enc(i)(?mac0, ?iv0, ?cg_cs) &*&
        take(GCM_ENT_SIZE, ent0) == take(GCM_ENT_SIZE, cs_content) &*&
        [_]public_generated(polarssl_pub(pub))(take(GCM_ENT_SIZE, ent0)) &*&
        GCM_ENT_SIZE <= length(cs_content) &*&
        GCM_ENT_SIZE <= length(ent0) &*&
        drop(GCM_ENT_SIZE, ent0) == cons(length(mac0), append(mac0, iv0)) &*&
        cg_cs == drop(GCM_ENT_SIZE, cs_content) &*&
        ITEM_CONSTRAINTS_CG(cg_cs, cg_auth_encrypted(p0, c0, mac0, ?cs_pay1, iv0)) &*&
        ITEM_CONSTRAINTS_PAY(cs_pay1, [_]pub(symmetric_key_item(p0, c0)));
    case asymmetric_encrypted_item(p0, c0, pay0, ent0): return
      tag == TAG_ASYMMETRIC_ENC &*&
        ITEM_CONSTRAINTS_CG(cs_content, cg_asym_encrypted(p0, c0, ?cs_pay1, ent0)) &*&
        ITEM_CONSTRAINTS_PAY(cs_pay1, [_]pub(public_key_item(p0, c0)));
    case asymmetric_signature_item(p0, c0, pay0, ent0): return
      tag == TAG_ASYMMETRIC_SIG &*&
        ITEM_CONSTRAINTS_CG(cs_content, cg_asym_signature(p0, c0, ?cs_pay1, ent0)) &*&
        ITEM_CONSTRAINTS_PAY(cs_pay1, [_]pub(private_key_item(p0, c0)));
  }
;

lemma void well_formed_item_constraints(item i1, item i2);
  requires [_]item_constraints(i1, ?cs, ?pub);
  ensures  [_]well_formed_item_chars(i2)(cs);

lemma void item_constraints_deterministic(list<char> cs1, list<char> cs2, item i);
  requires true == well_formed_item(i) &*&
           [_]item_constraints(i, cs1, ?pub) &*&
           [_]item_constraints(i, cs2, pub);
  ensures  col || cs1 == cs2;

lemma void item_constraints_injective(item i1, item i2, list<char> cs);
  requires [_]item_constraints(i1, cs, ?pub) &*&
           [_]item_constraints(i2, cs, pub);
  ensures  col || i1 == i2;

@*/

char item_tag(char* content, int size);
  /*@ requires [?f1]crypto_chars(secret, content, size, ?cs) &*&
               [_]item_constraints(?i, cs, ?pub) &*&
               [_]public_invar(polarssl_pub(pub)); @*/
  /*@ ensures  [f1]crypto_chars(secret, content, size, cs) &*&
               head(cs) == result &*&
               take(TAG_LENGTH, cs) == full_tag(result); @*/

void write_tag(char* buffer, char tag);
  //@ requires chars(buffer, TAG_LENGTH, _);
  /*@ ensures  chars(buffer, TAG_LENGTH, ?cs) &*&
               head(cs) == tag &*& cs == full_tag(tag); @*/

void check_tag(char* buffer, char tag);
  //@ requires [?f]chars(buffer, TAG_LENGTH, ?cs);
  /*@ ensures  [f]chars(buffer, TAG_LENGTH, cs) &*&
               head(cs) == tag &*& cs == full_tag(tag); @*/

/*@
predicate check_tag2_ghost_args(bool sym, bool wrong_key,
                                int p_key, int c_key) = true;
@*/

void check_tag2(char* buffer, char tag);
  /*@ requires [_]public_invar(?pub) &*&
               [_]decryption_key_classifier(?key_classifier) &*&
               network_permission(?p) &*&
               [?f2]crypto_chars(?kind, buffer, ?size, ?cs) &*&
               size > TAG_LENGTH &*&
               check_tag2_ghost_args(?sym, ?wrong_key, ?p_key, ?c_key) &*&
               wrong_key ?
                 decryption_with_wrong_key(sym, p, ?s, p_key, c_key, cs) &*&
                 s == known_value(0, full_tag(tag))
               :
                 true; @*/
  /*@ ensures  network_permission(p) &*&
               [f2]crypto_chars(kind, buffer, size, cs) &*&
               head(cs) == tag &*& take(TAG_LENGTH, cs) == full_tag(tag) &*&
               [_]public_generated(pub)(take(TAG_LENGTH, cs)) &*&
               wrong_key ?
                 decryption_permission(p) &*&
                 key_classifier(p_key, c_key, sym) ? true : col
               :
                 true; @*/

#endif
