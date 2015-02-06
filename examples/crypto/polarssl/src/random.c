#include "random.h"

#include <stdlib.h>

void r_int(struct havege_state* state, int* i)
  /*@ requires [?f]havege_state_initialized(state) &*&
               polarssl_generated_values(?principal, ?count) &*&
               integer(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               polarssl_generated_values(principal, count + 1) &*&
               integer(i, _); @*/
{
  char* temp = (void*) i;
  //@ close random_request(principal, 0, false);
  if (havege_random(state, temp, sizeof(int)) != 0) abort();
  //@ open polarssl_cryptogram(temp, _, _, _);
  //@ chars_to_integer(temp);
}

void r_int_with_bounds(struct havege_state* state, int* i, 
                       int l_bound, int u_bound)
  /*@ requires [?f]havege_state_initialized(state) &*&
               polarssl_generated_values(?principal, ?count1) &*&
               0 <= l_bound &*& l_bound < u_bound &*& 
               integer(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               polarssl_generated_values(principal, ?count2) &*&
               count2 > count1 &*& integer(i, ?val) &*& 
               l_bound <= val &*& val <= u_bound; @*/
{
  r_int(state, i);
    
  while (*i <= l_bound && *i < INT_MAX)
    //@ requires integer(i, _);
    //@ ensures  integer(i, ?val) &*& l_bound <= val;
  {
    //@ integer_limits(i);
    *i = *i + (u_bound - l_bound);
  }
  //@ assert *i >= l_bound;
  while (*i >= u_bound && *i > INT_MIN)
    //@ requires integer(i, ?val1) &*& val1 >= l_bound;
    //@ ensures  integer(i, ?val2) &*& val2 >= l_bound &*& val2 <= u_bound;
  {
    //@ integer_limits(i);
    *i = *i - (u_bound - l_bound);
  }
}

void r_u_int(struct havege_state* state, unsigned int* i)
  /*@ requires [?f]havege_state_initialized(state) &*&
               polarssl_generated_values(?principal, ?count) &*&
               u_integer(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               polarssl_generated_values(principal, count + 1) &*&
               u_integer(i, _); @*/
{
  //@ u_integer_to_chars(i);
  //@ chars_to_integer(i);
  r_int(state, (void*) i);
  //@ integer_to_chars(i);
  //@ chars_to_u_integer(i);
}

void r_u_int_with_bounds(struct havege_state* state, unsigned int* i, 
                         unsigned int l_bound, unsigned int u_bound)
  /*@ requires [?f]havege_state_initialized(state) &*&
               polarssl_generated_values(?principal, ?count1) &*&
               l_bound < u_bound &*& u_bound <= INT_MAX &*& 
               u_integer(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               polarssl_generated_values(principal, ?count2) &*&
               count1 < count2 &*& u_integer(i, ?val) &*& 
               l_bound <= val &*& val <= u_bound; @*/
{
  int j;
  r_int_with_bounds(state, &j, (int) l_bound, (int) u_bound);
  *i = (unsigned int) j;
}
