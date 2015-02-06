#ifndef RANDOM_H
#define RANDOM_H

#include "../annotated_api/polarssl.h"

void r_int(struct havege_state* state, int* i);
  /*@ requires [?f]havege_state_initialized(state) &*&
               polarssl_generated_values(?principal, ?count) &*&
               integer(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               polarssl_generated_values(principal, count + 1) &*&
               integer(i, _); @*/

void r_int_with_bounds(struct havege_state* state, int* i, 
                         int l_bound, int u_bound);
  /*@ requires [?f]havege_state_initialized(state) &*&
               polarssl_generated_values(?principal, ?count1) &*&
               0 <= l_bound &*& l_bound < u_bound &*& 
               integer(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               polarssl_generated_values(principal, ?count2) &*&
               count2 > count1 &*& integer(i, ?val) &*& 
               l_bound <= val &*& val <= u_bound; @*/

void r_u_int(struct havege_state* state, unsigned int* i);
  /*@ requires [?f]havege_state_initialized(state) &*&
               polarssl_generated_values(?principal, ?count) &*&
               u_integer(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               polarssl_generated_values(principal, count + 1) &*&
               u_integer(i, _); @*/

void r_u_int_with_bounds(struct havege_state* state, unsigned int* i, 
                         unsigned int l_bound, unsigned int u_bound);
  /*@ requires [?f]havege_state_initialized(state) &*&
               polarssl_generated_values(?principal, ?count1) &*&
               l_bound < u_bound &*& u_bound <= INT_MAX &*& 
               u_integer(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               polarssl_generated_values(principal, ?count2) &*&
               count2 > count1 &*& u_integer(i, ?val) &*& 
               l_bound <= val &*& val <= u_bound; @*/

#endif
