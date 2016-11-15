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

fixpoint list<char> full_tag(char tag)
{
  return repeat(tag, nat_of_int(TAG_LENGTH));
}

fixpoint list<crypto_char> full_ctag(crypto_char ctag)
{
  return repeat(ctag, nat_of_int(TAG_LENGTH));
}

lemma void cs_to_ccs_repeat(char c, nat n);
  requires n != zero;
  ensures  repeat(c_to_cc(c), n) == cs_to_ccs(repeat(c, n)) &*&
           head(repeat(c_to_cc(c), n)) == c_to_cc(head(repeat(c, n)));

lemma void cs_to_ccs_full_tag(char c);
  requires true;
  ensures  full_ctag(c_to_cc(c)) == cs_to_ccs(full_tag(c)) &*&
           head(full_ctag(c_to_cc(c))) == c_to_cc(c) &*&
           head(full_tag(c)) == c;

fixpoint list<char> full_tag_for_item(item i)
{
  return full_tag(tag_for_item(i));
}

fixpoint list<crypto_char> full_ctag_for_item(item i)
{
  return full_ctag(c_to_cc(tag_for_item(i)));
}

lemma void cs_to_ccs_full_tag_for_item(item i);
  requires true;
  ensures  full_ctag_for_item(i) == cs_to_ccs(full_tag_for_item(i)) &*&
           head(full_ctag_for_item(i)) == c_to_cc(tag_for_item(i)) &*&
           head(full_tag_for_item(i)) == tag_for_item(i);

fixpoint bool well_formed(list<crypto_char> ccs, nat upper_bound)
{
  switch(upper_bound)
  {
    case succ(n):
      return
        //correct total length
        length(ccs) > TAG_LENGTH &&
        //correct tag
        take(TAG_LENGTH, ccs) == full_ctag(head(ccs));
// //   valid_tag(head(ccs)) && 
// //         //correct data_item
// //         (
// //           head(cs) != TAG_DATA ||
// //           true
// //         ) &&
// //         //correct pair_item
// //         (
// //           head(cs) != TAG_PAIR ||
// //           (
// //             length(cs) > TAG_LENGTH + 1 &&
// //             (
// //               INT_MIN <= head(drop(TAG_LENGTH, cs)) &&
// //               INT_MAX >= head(drop(TAG_LENGTH, cs)) ?
// //               (
// //                 //size of first part within C bounds
// //                 int_of_chars(take(sizeof(int), drop(TAG_LENGTH, cs))) > 0 &&
// //                 length(cs) > TAG_LENGTH + sizeof(int) +
// //                              int_of_chars(take(sizeof(int), drop(TAG_LENGTH, cs))) &&
// //                 well_formed(take(int_of_chars(take(sizeof(int), drop(TAG_LENGTH, cs))),
// //                                  drop(TAG_LENGTH + sizeof(int), cs)), n) &&
// //                 well_formed(drop(int_of_chars(take(sizeof(int), drop(TAG_LENGTH, cs))),
// //                                  drop(TAG_LENGTH + sizeof(int), cs)), n)
// //               )
// //               :
// //               (
// //                 //size of first part NOT within C bounds
// //                 //only 1 char reserved for size of first part
// //                 head(drop(TAG_LENGTH, cs)) > 0 &&
// //                 length(cs) > TAG_LENGTH + 1 + head(drop(TAG_LENGTH, cs)) &&
// //                 well_formed(take(head(drop(TAG_LENGTH, cs)),
// //                                  drop(TAG_LENGTH + 1, cs)), n) &&
// //                 well_formed(drop(head(drop(TAG_LENGTH, cs)),
// //                                  drop(TAG_LENGTH + 1, cs)), n)
// //               )
// //             )
// //           )
// //         ) &&
// //         //correct nonce_item
// //         (
// //           head(cs) != TAG_NONCE ||
// //           length(cs) == TAG_LENGTH + 1 + NONCE_SIZE
// //         ) &&
// //         //correct hash_item
// //         (
// //           head(cs) != TAG_HASH ||
// //           length(cs) == TAG_LENGTH + HASH_SIZE
// //         ) &&
// //         //correct symmetric_key_item
// //         (
// //           head(cs) != TAG_SYMMETRIC_KEY ||
// //           length(cs) == TAG_LENGTH + GCM_KEY_SIZE
// //         ) &&
// //         //correct public_key_item
// //         (
// //           head(cs) != TAG_PUBLIC_KEY ||
// //           length(cs) == TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE
// //         ) &&
// //         //correct private_key_item
// //         (
// //           head(cs) != TAG_PRIVATE_KEY ||
// //           length(cs) == TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE
// //         ) &&
// //         //correct hmac_item
// //         (
// //           head(cs) != TAG_HMAC ||
// //           length(cs) == TAG_LENGTH + HMAC_SIZE
// //         ) &&
// //         //correct symmetric_encrypted_item
// //         (
// //           head(cs) != TAG_SYMMETRIC_ENC ||
// //           length(cs) >= TAG_LENGTH + MINIMAL_STRING_SIZE + GCM_IV_SIZE
// //         ) &&
// //         //correct asymmetric_encrypted_item
// //         (
// //           head(cs) != TAG_ASYMMETRIC_ENC ||
// //           (length(cs) <= TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE &&
// //            length(cs) >= TAG_LENGTH + MINIMAL_STRING_SIZE)
// //         ) &&
// //         //correct asymmetric_signed_item
// //         (
// //           head(cs) != TAG_ASYMMETRIC_SIG ||
// //           (length(cs) <= TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE &&
// //            length(cs) >= TAG_LENGTH + MINIMAL_STRING_SIZE)
// //         );
    case zero:
      return false;
  }
}

// #define WELL_FORMED(CS_TAG, CS_CONT, TAG) \
//   { \
//     head_append(CS_TAG, CS_CONT); \
//     take_append(TAG_LENGTH, CS_TAG, CS_CONT); \
//     drop_append(TAG_LENGTH, CS_TAG, CS_CONT); \
//     assert length(append(CS_TAG, CS_CONT)) > TAG_LENGTH; \
//     assert head(append(CS_TAG, CS_CONT)) == TAG; \
//     assert true == valid_tag(head(append(CS_TAG, CS_CONT))); \
//     assert take(TAG_LENGTH, append(CS_TAG, CS_CONT)) == full_tag(head(append(CS_TAG, CS_CONT))); \
//     length_equals_nat_length(append(CS_TAG, CS_CONT)); \
//     switch(nat_length(append(CS_TAG, CS_CONT))) {case succ(s0): case zero:} \
//   }

lemma void well_formed_upper_bound(list<crypto_char> ccs,
                                   nat upper_bound1, nat upper_bound2);
  requires true == well_formed(ccs, upper_bound1) &*&
           length(ccs) <= int_of_nat(upper_bound2);
  ensures  true == well_formed(ccs, upper_bound2);

lemma char well_formed_valid_tag(list<crypto_char> ccs, nat len);
  requires true == well_formed(ccs, len);
  ensures  valid_tag(result) && head(ccs) == c_to_cc(result) &&
           take(TAG_LENGTH, ccs) == full_ctag(head(ccs));

predicate_ctor well_formed_item_ccs(item i)(list<crypto_char> ccs) =
  true == well_formed(ccs, nat_length(ccs))
;

predicate_ctor ill_formed_item_ccs(item i)(list<crypto_char> ccs) =
  false == well_formed(ccs, nat_length(ccs))
;

predicate_ctor ic_parts(item i)(list<crypto_char> ccs_tag,
                                list<crypto_char> ccs_cont) = true;
predicate_ctor ic_pair(item i)(list<crypto_char> ccs_f,
                               list<crypto_char> ccs_s) = true;
predicate_ctor ic_sym_enc(item i)(list<crypto_char> iv,
                                  list<crypto_char> cg_ccs) = true;
predicate_ctor ic_cg(item i)(list<crypto_char> ccs, cryptogram cg) = true;

#define IC_PUBLIC \
  [_]public_generated(polarssl_pub(pub))(ccs_cont) &*& \
  [_]public_generated(polarssl_pub(pub))(ccs)

#define IC_PUBLIC_IF_COLLISION \
  (col ? IC_PUBLIC : true)

#define IC_CG(CCS, CG) \
  length(CCS) >= MINIMAL_STRING_SIZE &*& \
  ic_cg(i)(CCS, ?cg) &*& cg == CG &*& \
  col || (CCS == ccs_for_cg(cg) && cg_is_generated(cg))

#define IC_PAY(PAY, NONE) \
  col ? true : \
  switch(pay0) \
  { \
    case some(pay1): \
      return [_]well_formed_item_ccs(i)(PAY) &*& \
            length(PAY) <= INT_MAX &*& \
            [_]item_constraints(pay1, PAY, pub); \
    case none: \
      return [_]ill_formed_item_ccs(i)(PAY) &*& \
            length(PAY) <= INT_MAX &*& \
            col ? true : [_]public_generated(polarssl_pub(pub))(PAY) &*& NONE; \
  } \

#define OPEN_ITEM_CONSTRAINTS(I, CCS, PUB) \
  if (true) \
  { \
    open [_]item_constraints(I, CCS, PUB); \
    assert [_]ic_parts(I)(?ccs_tag, ?ccs_cont); \
    take_append(TAG_LENGTH, ccs_tag, ccs_cont); \
    drop_append(TAG_LENGTH, ccs_tag, ccs_cont); \
    head_append(ccs_tag, ccs_cont); \
    cs_to_ccs_full_tag_for_item(I); \
  }

predicate item_constraints(item i, list<crypto_char> ccs, predicate(item) pub) =
  true == well_formed(ccs, nat_length(ccs)) &*& length(ccs) <= INT_MAX &*&
  ic_parts(i)(?ccs_tag, ?ccs_cont) &*& ccs == append(ccs_tag, ccs_cont) &*&
  length(ccs_tag) == TAG_LENGTH &*& ccs_tag == full_ctag(head(ccs_tag)) &*&
  head(ccs_tag) == c_to_cc(tag_for_item(i)) &*&
  [_]public_generated(polarssl_pub(pub))(ccs_tag) &*&
  IC_PUBLIC_IF_COLLISION &*&
  switch(i)
  {
    case data_item(cs1): return
        ccs_cont == cs_to_ccs(cs1) &*& IC_PUBLIC;
    case pair_item(f0, s0): return
        ic_pair(i)(?ccs_f0, ?ccs_s0) &*&
        [_]item_constraints(f0, ccs_f0, pub) &*&
        [_]item_constraints(s0, ccs_s0, pub) &*&
        length(ccs_cont) > sizeof(int) + length(ccs_f0) &*&
        take(sizeof(int), ccs_cont) ==
          cs_to_ccs(chars_of_unbounded_int(length(ccs_f0))) &*&
        drop(sizeof(int), ccs_cont) == append(ccs_f0, ccs_s0) &*&
        [_]public_generated(polarssl_pub(pub))(take(sizeof(int), ccs_cont));
    case nonce_item(p0, c0, inc0): return
        ccs_cont == cons(c_to_cc(inc0), ?cs_cg) &*&
        [_]public_generated(polarssl_pub(pub))(cons(c_to_cc(inc0), nil)) &*&
        length(cs_cg) == NONCE_SIZE &*&
        IC_CG(cs_cg, cg_nonce(p0, c0));
    case hash_item(pay0): return
        length(ccs_cont) == HASH_SIZE &*&
        IC_CG(ccs_cont, cg_hash(?cs_pay1)) &*&
        IC_PAY(cs_pay1, true);
    case symmetric_key_item(p0, c0): return
        length(ccs_cont) == GCM_KEY_SIZE &*&
        IC_CG(ccs_cont, cg_symmetric_key(p0, c0));
    case public_key_item(p0, c0): return
        length(ccs_cont) == RSA_SERIALIZED_KEY_SIZE &*&
        IC_CG(ccs_cont, cg_public_key(p0, c0));
    case private_key_item(p0, c0): return
        length(ccs_cont) == RSA_SERIALIZED_KEY_SIZE &*&
        IC_CG(ccs_cont, cg_private_key(p0, c0));
    case hmac_item(p0, c0, pay0): return
        IC_CG(ccs_cont, cg_hmac(p0, c0, ?cs_pay1)) &*&
        IC_PAY(cs_pay1, [_]pub(symmetric_key_item(p0, c0)));
    case symmetric_encrypted_item(p0, c0, pay0, ent0): return
        ic_sym_enc(i)(?iv0, ?cg_ccs) &*&
        take(GCM_IV_SIZE, ent0) == take(GCM_IV_SIZE, ccs_cont) &*&
        [_]public_generated(polarssl_pub(pub))(take(GCM_IV_SIZE, ent0)) &*&
        GCM_IV_SIZE <= length(ent0) &*&
        drop(GCM_IV_SIZE, ent0) == iv0 &*&
        cg_ccs == drop(GCM_IV_SIZE, ccs_cont) &*&
        IC_CG(cg_ccs, cg_auth_encrypted(p0, c0, ?cs_pay1, iv0)) &*&
        IC_PAY(cs_pay1, [_]pub(symmetric_key_item(p0, c0)));
    case asymmetric_encrypted_item(p0, c0, pay0, ent0): return
        IC_CG(ccs_cont, cg_asym_encrypted(p0, c0, ?cs_pay1, ent0)) &*&
        IC_PAY(cs_pay1, [_]pub(public_key_item(p0, c0)));
    case asymmetric_signature_item(p0, c0, pay0, ent0): return
        IC_CG(ccs_cont, cg_asym_signature(p0, c0, ?cs_pay1, ent0)) &*&
        IC_PAY(cs_pay1, [_]pub(private_key_item(p0, c0)));
  }
;

lemma void well_formed_item_constraints(item i1, item i2);
  requires [_]item_constraints(i1, ?ccs, ?pub);
  ensures  [_]well_formed_item_ccs(i2)(ccs);

lemma void item_constraints_deterministic(list<crypto_char> ccs1,
                                          list<crypto_char> ccs2, item i);
  requires true == well_formed_item(i) &*&
           [_]item_constraints(i, ccs1, ?pub) &*&
           [_]item_constraints(i, ccs2, pub);
  ensures  col || ccs1 == ccs2;

lemma void item_constraints_injective(item i1, item i2, list<crypto_char> ccs);
  requires [_]item_constraints(i1, ccs, ?pub) &*&
           [_]item_constraints(i2, ccs, pub);
  ensures  col || i1 == i2;

@*/

char item_tag(char* content, int size);
  /*@ requires [?f1]crypto_chars(secret, content, size, ?ccs) &*&
               [_]item_constraints(?i, ccs, ?pub) &*&
               [_]public_invar(polarssl_pub(pub)); @*/
  /*@ ensures  [f1]crypto_chars(secret, content, size, ccs) &*&
               result == tag_for_item(i) &*&
               head(ccs) == c_to_cc(result) &*&
               take(TAG_LENGTH, ccs) == full_ctag(head(ccs)); @*/

void write_tag(char* buffer, char tag);
  //@ requires chars(buffer, TAG_LENGTH, _);
  /*@ ensures  chars(buffer, TAG_LENGTH, ?cs) &*&
               head(cs) == tag &*& cs == full_tag(tag); @*/

void check_tag(char* buffer, char tag);
  //@ requires [?f]chars(buffer, TAG_LENGTH, ?cs);
  /*@ ensures  [f]chars(buffer, TAG_LENGTH, cs) &*&
               head(cs) == tag &*& cs == full_tag(tag); @*/

/*@
predicate check_tag2_args(bool sym, bool garbage, int p_key,
                          int c_key, list<crypto_char> ccs_rest) = true;
@*/

void check_tag2(char* buffer, char tag);
  /*@ requires [_]public_invar(?pub) &*&
               [_]decryption_key_classifier(?key_classifier) &*&
               network_permission(?p) &*&
               [?f2]crypto_chars(normal, buffer, TAG_LENGTH, ?ccs) &*&
               check_tag2_args(?sym, ?garbage, ?p_key, ?c_key, ?rest_ccs) &*&
               garbage ?
                 decryption_garbage(sym, p, ?s, p_key, c_key,
                                    append(ccs, rest_ccs)) &*&
                 s == known_value(0, full_ctag(c_to_cc(tag)))
               :
                 true; @*/
  /*@ ensures  network_permission(p) &*&
               [f2]crypto_chars(normal, buffer, TAG_LENGTH, ccs) &*&
               head(ccs) == c_to_cc(tag) &*& ccs == full_ctag(head(ccs)) &*&
               garbage ?
                 decryption_permission(p) &*&
                 key_classifier(p_key, c_key, sym) ? true : col
               :
                 true; @*/

#endif
