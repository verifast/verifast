#include "havege_util.h"

#include <stdlib.h>

void r_int(struct havege_state* state, int* i)
  /*@ requires [_]public_invar(?pub) &*&
               [?f]havege_state_initialized(state) &*&
               random_permission(?principal, ?count) &*&
               havege_util(pub, ?proof_pred, principal) &*&
               int_(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               random_permission(principal, count + 1) &*&
               havege_util(pub, proof_pred, principal) &*&
               integer(i, _); @*/
{
  //@ open havege_util(pub, proof_pred, principal);
  //@ assert is_principal_with_public_nonces(?proof, pub, proof_pred, principal);
  char* temp = (void*) i;
  //@ close random_request(principal, 0, false);
  //@ int__to_chars_(i);
  if (havege_random(state, temp, sizeof(int)) != 0) abort();
  //@ open cryptogram(temp, ?l, ?cs, ?random);
  /*@ if (!col)
      {
        proof(random);
        public_cg_ccs(random);
        public_crypto_chars(temp, l);
      }
      else
      {
        crypto_chars_to_chars(temp, l);
      }
  @*/
  //@ chars_to_integer(temp);
  //@ close havege_util(pub, proof_pred, principal);
}

void r_int_with_bounds(struct havege_state* state, int* i, 
                       int l_bound, int u_bound)
  /*@ requires [_]public_invar(?pub) &*&
               [?f]havege_state_initialized(state) &*&
               random_permission(?principal, ?count1) &*&
               havege_util(pub, ?proof_pred, principal) &*&
               0 <= l_bound &*& l_bound < u_bound &*& 
               *i |-> _; @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               random_permission(principal, ?count2) &*&
               havege_util(pub, proof_pred, principal) &*&
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
  /*@ requires [_]public_invar(?pub) &*&
               [?f]havege_state_initialized(state) &*&
               random_permission(?principal, ?count) &*&
               havege_util(pub, ?proof_pred, principal) &*&
               u_integer(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               random_permission(principal, count + 1) &*&
               havege_util(pub, proof_pred, principal) &*&
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
  /*@ requires [_]public_invar(?pub) &*&
               [?f]havege_state_initialized(state) &*&
               random_permission(?principal, ?count1) &*&
               havege_util(pub, ?proof_pred, principal) &*&
               l_bound < u_bound &*& u_bound <= INT_MAX &*& 
               *i |-> _; @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               random_permission(principal, ?count2) &*&
               havege_util(pub, proof_pred, principal) &*&
               count1 < count2 &*& u_integer(i, ?val) &*& 
               l_bound <= val &*& val <= u_bound; @*/
{
  int j;
  r_int_with_bounds(state, &j, (int) l_bound, (int) u_bound);
  *i = (unsigned int) j;
}