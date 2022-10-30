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

#include "mbedTLS_definitions.h"

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
               malloc_block(result, size) &*& chars_(result, size, ?cs) &*&
               object_pointer_within_limits(result, size) == true; @*/

void write_buffer(char **target, const char *source, int length);
  /*@ requires pointer(target, ?t) &*& chars_(t, length, ?cs) &*&
               [?f]crypto_chars(?kind, source, length, ?ccs0) &*&
               length > 0 &*& kind == normal ||
                 (kind == secret && length >= MINIMAL_STRING_SIZE)
               &*& length <= INT_MAX &*& pointer_within_limits(t + length) == true; @*/
  /*@ ensures  pointer(target, t + length) &*&
               crypto_chars(kind, t, length, ccs0) &*&
               [f]crypto_chars(kind, source, length, ccs0); @*/

///////////////////////////////////////////////////////////////////////////////
// Auxiliary lemmas ///////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

// cs_to_ccs and ints

lemma void equal_append_chars_of_int(int i1, int i2, list<char> cs1,
                                                     list<char> cs2);
  requires INT_MIN <= i1 && i1 <= INT_MAX &*& INT_MIN <= i2 && i2 <= INT_MAX &*&
           append(chars_of_int(i1), cs1) == append(chars_of_int(i2), cs2);
  ensures  cs1 == cs2 &*& i1 == i2;

fixpoint list<crypto_char> ccs_of_int(int i)
{
  return cs_to_ccs(chars_of_int(i));
}

lemma void equal_append_ccs_of_int(int i1, int i2, list<crypto_char> ccs1,
                                                   list<crypto_char> ccs2);
  requires INT_MIN <= i1 && i1 <= INT_MAX &*& INT_MIN <= i2 && i2 <= INT_MAX &*&
           append(ccs_of_int(i1), ccs1) == append(ccs_of_int(i2), ccs2);
  ensures  ccs1 == ccs2 &*& i1 == i2;

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

lemma void chars_of_unbounded_int_bounds(int i);
  requires true;
  ensures  INT_MIN <= i && i <= INT_MAX ?
             INT_MIN <= head(chars_of_unbounded_int(i)) &*&
             head(chars_of_unbounded_int(i)) <= INT_MAX
           :
             head(chars_of_unbounded_int(i)) == i;

// nat_length

fixpoint nat nat_length<T>(list<T> xs)
{
  switch(xs)
  {
    case nil : return zero;
    case cons(x0, xs0) : return succ(nat_length(xs0));
  }
}

fixpoint list<T> repeat<T>(T t, nat n)
{
  switch(n)
  {
    case succ(n0): return cons(t, repeat(t, n0));
    case zero:    return nil;
  }
}

lemma void repeat_length<T>(T t, nat n);
  requires true;
  ensures  nat_length(repeat(t, n)) == n;

lemma void length_equals_nat_length<T>(list<T> xs);
  requires true;
  ensures  length(xs) == int_of_nat(nat_length(xs));

lemma void int_of_nat_injective(nat n1, nat n2);
  requires int_of_nat(n1) == int_of_nat(n2);
  ensures  n1 == n2;

@*/

#endif
