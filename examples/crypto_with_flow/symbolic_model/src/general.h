#ifndef GENERAL_H
#define GENERAL_H

#include "../include/symbolic.h"

///////////////////////////////////////////////////////////////////////////////
// Stdlib includes ////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

///////////////////////////////////////////////////////////////////////////////
// Ghost includes /////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ #include <listex.gh>

///////////////////////////////////////////////////////////////////////////////
// PolarSLL includes + config /////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

#include "polarssl_definitions/polarssl_definitions.h"

#define MAX_PACKAGE_SIZE 8192

#define MIN_DATA_SIZE 4
#define NONCE_SIZE 16
#define HASH_SIZE 64
#define HMAC_SIZE 64
#define GCM_IV_SIZE 16
#define GCM_MAC_SIZE 16
#define GCM_KEY_SIZE 32
#define RSA_KEY_SIZE 256
#define RSA_BIT_KEY_SIZE (8 * RSA_KEY_SIZE)
#define RSA_SERIALIZED_KEY_SIZE 2048

///////////////////////////////////////////////////////////////////////////////
// Auxiliary functions ////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void *malloc_wrapper(int size);
  //@ requires 0 <= size;
  /*@ ensures  result != 0 &*&
               malloc_block(result, size) &*& chars(result, size, ?cs) &*&
               true == ((char *)0 < result &&
               result + size <= (char *)UINTPTR_MAX); @*/

void write_buffer(char **target, const char *source, int length);
  /*@ requires pointer(target, ?t) &*& chars(t, length, ?cs) &*&
               [?f]crypto_chars(?kind, source, length, ?cs0) &*& 
               length > 0 &*& kind == normal || 
                 (kind == secret && length >= MINIMAL_STRING_SIZE) 
               &*& length <= INT_MAX &*& t + length <= (void*) UINTPTR_MAX; @*/
  /*@ ensures  pointer(target, t + length) &*&
               crypto_chars(kind, t, length, cs0) &*&
               [f]crypto_chars(kind, source, length, cs0); @*/

///////////////////////////////////////////////////////////////////////////////
// Auxiliary lemmas ///////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

lemma void equal_append_chars_of_int(int i1, int i2,
                                     list<char> cs1, list<char> cs2);
  requires INT_MIN <= i1 && i1 <= INT_MAX &*& INT_MIN <= i2 && i2 <= INT_MAX &*&
           append(chars_of_int(i1), cs1) == append(chars_of_int(i2), cs2);
  ensures  cs1 == cs2 &*& i1 == i2;

lemma void drop_drop(int i1, int i2, list<char> cs);
  requires i1 >= 0 &*& i2 >= 0 &*& i1 + i2 < length(cs);
  ensures  drop(i1, drop(i2, cs)) == drop(i1 + i2, cs);

lemma void equal_list_equal_prefix(list<char> cs1, list<char> cs2,
                                   list<char> cs3);
  requires append(cs1, cs3) == append(cs2, cs3);
  ensures  cs1 == cs2;

lemma void equal_append(list<char> cs1, list<char> cs11,
                        list<char> cs2, list<char> cs22);
  requires length(cs1) == length(cs2) &*&
           append(cs1, cs11) == append(cs2, cs22);
  ensures  cs1 == cs2 && cs11 == cs22;

lemma void equal_double_triple_append(
                              list<char> cs1, list<char> cs2, list<char> cs3,
                              list<char> cs4, list<char> cs5, list<char> cs6);
  requires true;
  ensures  append(cs1, append(cs2, append(cs3,
           append(cs4, append(cs5, cs6)))))
           ==
           append(
             append(cs1, append(cs2, cs3)),
             append(cs4, append(cs5, cs6)));

fixpoint nat nat_length<T>(list<T> cs)
{
  switch(cs)
  {
    case nil : return zero;
    case cons(c, cs0) : return succ(nat_length(cs0));
  }
}

lemma void length_equals_nat_length(list<char> cs);
  requires true;
  ensures  length(cs) == int_of_nat(nat_length(cs));

lemma void int_of_nat_injective(nat n1, nat n2);
  requires int_of_nat(n1) == int_of_nat(n2);
  ensures  n1 == n2;

fixpoint int unbounded_int_of_chars(list<char> cs)
{
  return
    length(cs) == sizeof(int) ?
      int_of_chars(cs)
    :
      head(cs)
  ;
}

fixpoint list<char> chars_of_unbounded_int(int i)
{
  return
    INT_MIN <= i && i <= INT_MAX ?
      chars_of_int(i)
    :
      cons(i, nil)
  ;
}

lemma void head_append<t>(list<t> xs, list<t> ys);
  requires length(xs) > 0;
  ensures head(xs) == head(append(xs, ys));

lemma void head_mem<t>(list<t> l);
  requires length(l) > 0;
  ensures  true == mem(head(l), l);

lemma void take_1<t>(list<t> xs);
  requires length(xs) > 0;
  ensures  take(1, xs) == cons(head(xs), nil);

lemma void chars_of_unbounded_int_bounds(int i);
  requires true;
  ensures  INT_MIN <= i && i <= INT_MAX ?
             INT_MIN <= head(chars_of_unbounded_int(i)) &*&
             head(chars_of_unbounded_int(i)) <= INT_MAX
           :
             head(chars_of_unbounded_int(i)) == i;

fixpoint list<char> repeat(char c, nat length)
{
  switch(length)
  {
    case succ(n): return cons(c, repeat(c, n));
    case zero:    return nil;
  }
}

lemma void repeat_length(char c, nat n);
  requires true;
  ensures  nat_length(repeat(c, n)) == n;

@*/

#endif
