#ifndef GENERAL_H
#define GENERAL_H

#include "../include/cryptolib.h"

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
// PolarSLL config ////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

#include "../include/polarssl.h"

#define MAX_PACKAGE_SIZE 8192

#define NONCE_SIZE   64
#define HMAC_SIZE    64
#define AES_IV_SIZE  16
#define AES_KEY_SIZE 256

#define RSA_KEY_SIZE 2048
#define RSA_SERIALIZED_KEY_SIZE 2048

///////////////////////////////////////////////////////////////////////////////
// Auxiliary functions ////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void *malloc_wrapper(int size);
  //@ requires 0 <= size;
  /*@ ensures  result != 0 &*&
               malloc_block(result, size) &*& chars(result, size, ?cs) &*&
               true == ((char *)0 < result &&
               result + size <= (char *)UINTPTR_MAX);
  @*/

void write_buffer(char **target, const char *source, int length);
  /*@ requires pointer(target, ?t) &*& chars(t, length, ?cs) &*&
               [?f]chars(source, length, ?cs0) &*&
               length > 0 &*& length <= INT_MAX &*&
               t + length <= (void*) UINTPTR_MAX;
  @*/
  /*@ ensures  pointer(target, t + length) &*& chars(t, length, cs0) &*&
               [f]chars(source, length, cs0);
  @*/

///////////////////////////////////////////////////////////////////////////////
// Auxiliary predicates ///////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

predicate hide_chars(char *buffer, int length, list<char> cs) =
  chars(buffer, length, cs)
;

@*/

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

@*/

#endif
