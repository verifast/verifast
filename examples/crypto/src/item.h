#ifndef ITEM_H
#define ITEM_H

#include "general.h"

struct item
{
  // 0   = data_item
  // 1   = pair_item
  // 2   = nonce_item
  // 3   = key_item
  // 4   = hmac_item
  // 5   = encrypted_item
  int tag;

  int size;
  char* content;
};

/*@

predicate item(struct item *item, item i) =
  item != 0 &*&
  item->tag     |-> ?tag &*&
  item->size    |-> ?size &*&
  item->content |-> ?content &*&
    chars(content, size, ?cs) &*&
    malloc_block_chars(content, size) &*&
  malloc_block_item(item) &*&

  tag == tag_for_item(i) &*&
  0 < size && size <= INT_MAX - 2 * sizeof(int) &&
  if_no_collision(item_constraints(i, tag, size, cs))
;

lemma_auto void non_zero_items()
  requires item(?item, ?i);
  ensures  item(item, i) &*& item != 0;
{
  open item(item, i);
  close item(item, i);
}

fixpoint int tag_for_item(item i)
{
  switch (i)
  {
    case data_item(d0):
      return 0;
    case pair_item(f0, s0):
      return 1;
    case nonce_item(p0, c0, inc0, i0):
      return 2;
    case key_item(p0, c0, k0, i0):
      return 3;
    case hmac_item(k0, pay0):
      return 4;
    case encrypted_item(k0, pay0, ent0):
      return 5;
  }
}

@*/

void check_valid_item_tag(int tag);
  //@ requires true;
  //@ ensures  tag >= 0 && tag <= 5;

void check_valid_item_size(int size);
  //@ requires true;
  //@ ensures  2 * sizeof(int) < size && size < INT_MAX;

void check_valid_item_chars_size(int cs_size);
  //@ requires true;
  //@ ensures  0 < cs_size && cs_size < INT_MAX - 2 * sizeof(int);

void check_valid_item_sizes(int size, int cs_size);
  //@ requires true;
  /*@ ensures  2 * sizeof(int) < size && size < INT_MAX &*&
               0 < cs_size && cs_size < INT_MAX - 2 * sizeof(int) &*& 
               size == cs_size + 2 * sizeof(int); @*/

/*@
fixpoint item dummy_item_for_tag(int tag)
{
  return  (tag == 1) ?
          pair_item(data_item(0), data_item(0))
        : (tag == 2) ?
          nonce_item(0, 0, 0, 0)
        : (tag == 3) ?
          key_item(0, 0, symmetric_key, 0)
        : (tag == 4) ?
          hmac_item(data_item(0), data_item(0))
        : (tag == 5) ?
          encrypted_item(data_item(0), data_item(0), nil)
        :
          data_item(0);
}

lemma void dummy_item_for_tag_has_valid_tag(int tag)
  requires 0 <= tag && tag <= 5;
  ensures  tag == tag_for_item(dummy_item_for_tag(tag));
{
  if (tag <= 0)
    assert tag == tag_for_item(dummy_item_for_tag(tag));
  else if (tag <= 1)
    assert tag == tag_for_item(dummy_item_for_tag(tag));
  else if (tag <= 2)
    assert tag == tag_for_item(dummy_item_for_tag(tag));
  else if (tag <= 3)
    assert tag == tag_for_item(dummy_item_for_tag(tag));
  else if (tag <= 4)
    assert tag == tag_for_item(dummy_item_for_tag(tag));
  else if (tag <= 5)
    assert tag == tag_for_item(dummy_item_for_tag(tag));
  else
    assert false;
}

fixpoint list<char> chars_for_item(item i)
{
  switch(i)
  {
    case data_item(d):
      return chars_of_int(d);
    case pair_item(f, s):
      return append(chars_of_int(tag_for_item(f)),
               append(chars_of_int(length(chars_for_item(f))),
                 append(chars_for_item(f),
                   append(chars_of_int(tag_for_item(s)),
                     append(chars_of_int(length(chars_for_item(s))),
                            chars_for_item(s))))));
    case nonce_item(p0, c0, inc0, i0):
      return append(chars_of_int(inc0), 
               havege_chars_for_polarssl_item(
               polarssl_havege_item(p0, c0)));
    case key_item(p0, c0, k0, i0): return
      switch (k0)
      {
        case symmetric_key:
          return cons('a', havege_chars_for_polarssl_item(
                                         polarssl_havege_item(p0, c0)));
        case public_key:
          return cons('b', rsa_public_key_chars_for_polarssl_item(
                               polarssl_rsa_public_key_item(p0, c0)));
        case private_key:
          return cons('c', rsa_private_key_chars_for_polarssl_item(
                               polarssl_rsa_private_key_item(p0, c0)));
      };
    case hmac_item(k0, pay0):
      return sha512_chars_for_polarssl_item(polarssl_sha512_item(
          append(chars_of_int(tag_for_item(k0)),
            append(chars_of_int(length(chars_for_item(k0))),
              chars_for_item(k0))),
          append(chars_of_int(tag_for_item(pay0)),
            append(chars_of_int(length(chars_for_item(pay0))),
              chars_for_item(pay0)))
        ));
     case encrypted_item(key0, pay0, ent0): return
        switch (key0)
        {
          case data_item(d1): return nil;
          case pair_item(f1, s1): return nil;
          case nonce_item(p1, c1, inc1, i1): return nil;
          case hmac_item(k1, pay1): return nil;
          case encrypted_item(k1, pay1, ent1): return nil;
          case key_item(p1, c1, k1, i1): return
          switch (k1)
          {
            case symmetric_key: return cons('a',
              append(ent0,
                aes_chars_for_polarssl_item(
                  polarssl_aes_encrypted_item(
                    append(chars_of_int(tag_for_item(key0)),
                      append(chars_of_int(length(chars_for_item(key0))),
                              chars_for_item(key0))),
                    int_of_chars(take(sizeof(int), ent0)),
                    drop(sizeof(int), ent0),
                          append(chars_of_int(tag_for_item(pay0)),
                            append(chars_of_int(length(chars_for_item(pay0))),
                                  chars_for_item(pay0)))))));
            case public_key: return cons('b',
              rsa_encrypted_chars_for_polarssl_item(
                polarssl_rsa_encrypted_item(p1, c1, 
                  append(chars_of_int(tag_for_item(pay0)),
                    append(chars_of_int(length(chars_for_item(pay0))),
                           chars_for_item(pay0))), ent0)));
            case private_key: return nil;
          };
        };
  }
}

fixpoint list<char> extended_chars_for_item(item i)
{
  return append(chars_of_int(tag_for_item(i)),
           append(chars_of_int(length(chars_for_item(i))),
                  chars_for_item(i)));
}

fixpoint bool item_constraints_recursive(item i)
{
  switch (i)
  {
    case data_item(d0): 
        return INT_MIN <= d0 && d0 <= INT_MAX;
    case pair_item(f0, s0): return
        0 < length(chars_for_item(f0)) &&
        length(chars_for_item(f0)) <= INT_MAX - 2 * sizeof(int) &&
        0 < length(chars_for_item(s0)) &&
        length(chars_for_item(s0)) <= INT_MAX - 2 * sizeof(int) &&
        item_constraints_recursive(f0) && 
        item_constraints_recursive(s0);
    case nonce_item(p0, c0, inc0, i0): return
        NONCE_SIZE == length(
          havege_chars_for_polarssl_item(polarssl_havege_item(p0, c0))) &&
        i0 == info_for_polarssl_item(polarssl_havege_item(p0, c0)) &&
        0 <= inc0 && inc0 <= INT_MAX;
    case key_item(p0, c0, k0, i0): return
        switch(k0)
        {
          case symmetric_key: return
            AES_KEY_SIZE - 2 * sizeof(int) - sizeof(char) == length(
              havege_chars_for_polarssl_item(polarssl_havege_item(p0, c0))) &&
              i0 == info_for_polarssl_item(polarssl_havege_item(p0, c0));
          case public_key: return
              RSA_SERIALIZED_KEY_SIZE ==
              length(rsa_public_key_chars_for_polarssl_item(
                polarssl_rsa_public_key_item(p0, c0)
              )) &&
              i0 == info_for_polarssl_item(polarssl_rsa_public_key_item(p0, c0)) &&
              i0 == info_for_polarssl_item(polarssl_rsa_private_key_item(p0, c0));
          case private_key: return
              RSA_SERIALIZED_KEY_SIZE ==
              length(rsa_private_key_chars_for_polarssl_item(
                polarssl_rsa_private_key_item(p0, c0)
              )) &&
              i0 == info_for_polarssl_item(polarssl_rsa_public_key_item(p0, c0)) &&
              i0 == info_for_polarssl_item(polarssl_rsa_private_key_item(p0, c0));
        };
    case hmac_item(k0, pay0): return
        switch (k0)
        {
          case data_item(d1): return false;
          case pair_item(f1, s1): return false;
          case nonce_item(p1, c1, inc1, i1): return false;
          case key_item(p1, c1, k1, i1): return true;
          case hmac_item(k1, pay1): return false;
          case encrypted_item(k1, pay1, ent1): return false;
        } &&
        0 < length(chars_for_item(k0)) &&
        length(chars_for_item(k0)) <= INT_MAX - 2 * sizeof(int) &&
        0 < length(chars_for_item(pay0)) &&
        length(chars_for_item(pay0)) <= INT_MAX - 2 * sizeof(int) &&
        item_constraints_recursive(k0) && 
        item_constraints_recursive(pay0);
    case encrypted_item(k0, pay0, ent0): return 
        switch (k0)
        {
          case data_item(d1): return false;
          case pair_item(f1, s1): return false;
          case nonce_item(p1, c1, inc1, i1): return false;
          case key_item(p1, c1, k1, i1): return
            0 < length(chars_for_item(pay0)) &&
            length(chars_for_item(pay0)) <= INT_MAX - 2 * sizeof(int) &&
            item_constraints_recursive(pay0) &&
            0 < length(chars_for_item(k0)) &&
            length(chars_for_item(k0)) <= INT_MAX - 2 * sizeof(int) &&
            item_constraints_recursive(k0) &&
            switch (k1)
            {
              case symmetric_key: return
                i1 == info_for_polarssl_item(polarssl_havege_item(p1, c1)) &&
                length(ent0) == sizeof(int) + AES_IV_SIZE &&
                0 <= int_of_chars(take(sizeof(int), ent0)) &&
                16 > int_of_chars(take(sizeof(int), ent0));
              case public_key: return
                i1 == info_for_polarssl_item(polarssl_rsa_private_key_item(p1, c1));
              case private_key: return false;
            };
          case hmac_item(k1, pay1): return false;
          case encrypted_item(k1, pay1, ent1): return false;
        };
  }
}

fixpoint bool item_constraints(item i, int tag, int size, list<char> cs)
{
  return tag == tag_for_item(i) && 
         0 < size && size <= INT_MAX - 2 * sizeof(int) &&
         cs == chars_for_item(i) &&
         item_constraints_recursive(i);
}

lemma_auto void tag_for_item_valid_int(item i)
  requires true;
  ensures  INT_MIN <= tag_for_item(i) && tag_for_item(i) <= INT_MAX;
{
  switch (i)
  {
    case data_item(d0):
    case pair_item(f0, s0):
    case nonce_item(p0, c0, inc0, i0):
    case key_item(p0, c0, k0, i0):
    case hmac_item(k0, pay0):
    case encrypted_item(k0, pay0, ent0):
  }
}

lemma void chars_and_tag_for_item_injective(item i1, item i2);
  requires [?f0]polarssl_world<item>(?pub) &*&
           chars_for_item(i1) == chars_for_item(i2) &*&
           tag_for_item(i1) == tag_for_item(i2) &*&
           item_constraints(i1, tag_for_item(i1), length(chars_for_item(i1)),
                            chars_for_item(i1)) == true &*&
           item_constraints(i2, tag_for_item(i2), length(chars_for_item(i2)),
                            chars_for_item(i2)) == true;
  ensures  [f0]polarssl_world<item>(pub) &*&
           true == if_no_collision(i1 == i2);

lemma void extended_chars_for_item_injective(item i1, item i2);
  requires [?f0]polarssl_world<item>(?pub) &*&
           extended_chars_for_item(i1) == extended_chars_for_item(i2) &*&
           item_constraints(i1, tag_for_item(i1), length(chars_for_item(i1)),
                            chars_for_item(i1)) == true &*&
           item_constraints(i2, tag_for_item(i2), length(chars_for_item(i2)),
                            chars_for_item(i2)) == true;
  ensures  [f0]polarssl_world<item>(pub) &*&
           true == if_no_collision(i1 == i2);
@*/

#endif
