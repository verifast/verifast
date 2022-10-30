#include "item_tags.h"

/*@

lemma void cs_to_ccs_repeat(char c, nat n)
  requires n != zero;
  ensures  repeat(c_to_cc(c), n) == cs_to_ccs(repeat(c, n)) &*&
           head(repeat(c_to_cc(c), n)) == c_to_cc(head(repeat(c, n)));
{
  switch(n)
  {
    case succ(n0):
      if (n0 != zero) cs_to_ccs_repeat(c, n0);
    case zero:
  }
}

lemma void cs_to_ccs_full_tag(char c)
  requires true;
  ensures  full_ctag(c_to_cc(c)) == cs_to_ccs(full_tag(c)) &*&
           head(full_ctag(c_to_cc(c))) == c_to_cc(c) &*&
           head(full_tag(c)) == c;
{
  succ_int(TAG_LENGTH - 1);
  cs_to_ccs_repeat(c, nat_of_int(TAG_LENGTH));
}

lemma void cs_to_ccs_full_tag_for_item(item i)
  requires true;
  ensures  full_ctag_for_item(i) == cs_to_ccs(full_tag_for_item(i)) &*&
           head(full_ctag_for_item(i)) == c_to_cc(tag_for_item(i)) &*&
           head(full_tag_for_item(i)) == tag_for_item(i);
{
  cs_to_ccs_full_tag(tag_for_item(i));
}

@*/

void write_tag(char* buffer, char tag)
  //@ requires chars_(buffer, TAG_LENGTH, _);
  /*@ ensures  chars(buffer, TAG_LENGTH, ?cs) &*&
               head(cs) == tag &*& cs == full_tag(tag); @*/
{
  int offset = 0;
  while (offset < TAG_LENGTH)
    /*@ requires offset <= TAG_LENGTH &*&
                 true == ((char *)0 <= buffer + offset) &*&
                 pointer_within_limits(buffer + offset) == true &*&
                 chars_(buffer + offset, TAG_LENGTH - offset, ?cs0) &*&
                 offset != TAG_LENGTH || cs0 == nil; @*/
    /*@ ensures  chars(buffer + old_offset, TAG_LENGTH - old_offset, ?cs1) &*&
                 old_offset == TAG_LENGTH || head(cs1) == tag &*&
                 cs1 == repeat(tag, nat_of_int(TAG_LENGTH - old_offset)); @*/
  {
    //@ length_equals_nat_length(cs0);
    //@ chars__limits(buffer + offset);
    //@ open chars_(buffer + offset, TAG_LENGTH - offset, _);
    *(buffer + offset) = tag;
    offset = offset + 1;
    //@ open chars_(buffer + offset, TAG_LENGTH - offset, _);
    //@ close chars_(buffer + offset, TAG_LENGTH - offset, _);
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
                 pointer_within_limits(buffer + offset) == true &*&
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
{
  //@ open check_tag2_args(sym, garbage, p, p_key, c_key, rest_ccs);
  char tb[TAG_LENGTH];
  write_tag(tb, tag);
  //@ public_chars(tb, TAG_LENGTH);
  //@ chars_to_crypto_chars(tb, TAG_LENGTH);
  //@ cs_to_ccs_full_tag(tag);
  //@ MEMCMP_PUB(tb)
  //@ MEMCMP_PUB(buffer)
  if (crypto_memcmp(buffer, tb, TAG_LENGTH) != 0)
    abort_crypto_lib("Checking tag failed");
  //@ assert [f2]crypto_chars(?kind2, buffer, TAG_LENGTH, ccs);
  /*@ if (garbage)
      {
        assert decryption_garbage(sym, p, ?s, p_key, c_key, _);
        close exists(pair(nil, rest_ccs));
        close has_structure(append(ccs, rest_ccs), s);
        leak has_structure(append(ccs, rest_ccs), s);
        decryption_garbage(buffer, TAG_LENGTH, s);
      }
  @*/
  //@ crypto_chars_to_chars(tb, TAG_LENGTH);
}
