#ifndef ITEM_TAGS_H
#define ITEM_TAGS_H

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

#define TAG_LENGTH MINIMAL_STRING_SIZE

#include "general.h"

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

// e.g. full_tag_for_item(data_item(...)) == cons('a', cons('a', cons('a', ...)))
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

#define SWITCH_TAG(TAG) \
  if (true) \
  { \
    c_to_cc_inj(TAG, TAG_DATA); \
    c_to_cc_inj(TAG, TAG_PAIR); \
    c_to_cc_inj(TAG, TAG_NONCE); \
    c_to_cc_inj(TAG, TAG_HASH); \
    c_to_cc_inj(TAG, TAG_SYMMETRIC_KEY); \
    c_to_cc_inj(TAG, TAG_PUBLIC_KEY); \
    c_to_cc_inj(TAG, TAG_PRIVATE_KEY); \
    c_to_cc_inj(TAG, TAG_HMAC); \
    c_to_cc_inj(TAG, TAG_SYMMETRIC_ENC); \
    c_to_cc_inj(TAG, TAG_ASYMMETRIC_ENC); \
    c_to_cc_inj(TAG, TAG_ASYMMETRIC_SIG); \
  } \

@*/

void write_tag(char* buffer, char tag);
  //@ requires chars_(buffer, TAG_LENGTH, _);
  /*@ ensures  chars(buffer, TAG_LENGTH, ?cs) &*&
               head(cs) == tag &*& cs == full_tag(tag); @*/

void check_tag(char* buffer, char tag);
  //@ requires [?f]chars(buffer, TAG_LENGTH, ?cs);
  /*@ ensures  [f]chars(buffer, TAG_LENGTH, cs) &*&
               head(cs) == tag &*& cs == full_tag(tag); @*/

/*@
predicate check_tag2_args(bool sym, bool garbage, int p, int p_key,
                          int c_key, list<crypto_char> ccs_rest) = true;
@*/

void check_tag2(char* buffer, char tag);
  /*@ requires [_]public_invar(?pub) &*&
               [_]decryption_key_classifier(?key_classifier) &*&
               [?f2]crypto_chars(normal, buffer, TAG_LENGTH, ?ccs) &*&
               check_tag2_args(?sym, ?garbage, ?p, ?p_key, ?c_key, ?rest_ccs) &*&
               garbage ?
                 decryption_garbage(sym, p, ?s, p_key, c_key,
                                    append(ccs, rest_ccs)) &*&
                 s == known_value(0, full_ctag(c_to_cc(tag)))
               :
                 true; @*/
  /*@ ensures  [f2]crypto_chars(normal, buffer, TAG_LENGTH, ccs) &*&
               head(ccs) == c_to_cc(tag) &*& ccs == full_ctag(head(ccs)) &*&
               garbage ?
                 decryption_permission(p) &*&
                 key_classifier(p_key, c_key, sym) ? true : col
               :
                 true; @*/

#endif
