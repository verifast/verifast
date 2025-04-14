#ifndef HAVEGE_UTIL_H
#define HAVEGE_UTIL_H

#include "havege.h"

/*@

typedef lemma void principal_with_public_nonces(predicate(cryptogram) pub,
                                                predicate() proof_pred,
                                                int principal)
                                               (cryptogram nonce);
  requires  proof_pred() &*&
            [_]public_invar(pub) &*&
            nonce == cg_nonce(principal, _);
  ensures   proof_pred() &*&
            [_]pub(nonce);

predicate havege_util(predicate(cryptogram) pub, predicate() proof_pred, int principal)=
  is_principal_with_public_nonces(?proof, pub, proof_pred, principal) &*&
  proof_pred()
;

#define DEFAULT_HAVEGE_UTIL_INIT(PUB, PRED, PRINCIPAL) \
{ \
  lemma void principal_with_public_nonces(cryptogram nonce) \
    requires  nonce == cg_nonce(PRINCIPAL, _); \
    ensures   [_]PUB(nonce); \
  { \
    close PUB(nonce); \
    leak PUB(nonce); \
  } \
  produce_lemma_function_pointer_chunk(principal_with_public_nonces) : \
    principal_with_public_nonces(PUB, PRED, PRINCIPAL)(nonce_){call();} \
    {duplicate_lemma_function_pointer_chunk(principal_with_public_nonces); \
     duplicate_lemma_function_pointer_chunk(principal_with_public_nonces);}; \
  leak is_principal_with_public_nonces(_, PUB, PRED, PRINCIPAL); \
  close PRED(); \
  close havege_util(PUB, PRED, PRINCIPAL); \
}

#define DEFAULT_HAVEGE_UTIL_EXIT(PUB, PRED, PRINCIPAL) \
{ \
  open havege_util(PUB, PRED, PRINCIPAL); \
  leak is_principal_with_public_nonces(_, PUB, PRED, PRINCIPAL); \
  open PRED(); \
}

@*/

void r_int(struct havege_state* state, int* i);
  /*@ requires [_]public_invar(?pub) &*&
               [?f]havege_state_initialized(state) &*&
               random_permission(?principal, ?count) &*&
               havege_util(pub, ?proof_pred, principal) &*&
               *i |-> _; @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               random_permission(principal, count + 1) &*&
               havege_util(pub, proof_pred, principal) &*&
               integer(i, _); @*/

void r_int_with_bounds(struct havege_state* state, int* i, 
                       int l_bound, int u_bound);
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

void r_u_int(struct havege_state* state, unsigned int* i);
  /*@ requires [_]public_invar(?pub) &*&
               [?f]havege_state_initialized(state) &*&
               random_permission(?principal, ?count) &*&
               havege_util(pub, ?proof_pred, principal) &*&
               u_integer(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               random_permission(principal, count + 1) &*&
               havege_util(pub, proof_pred, principal) &*&
               u_integer(i, _); @*/

void r_u_int_with_bounds(struct havege_state* state, unsigned int* i, 
                         unsigned int l_bound, unsigned int u_bound);
  /*@ requires [_]public_invar(?pub) &*&
               [?f]havege_state_initialized(state) &*&
               random_permission(?principal, ?count1) &*&
               havege_util(pub, ?proof_pred, principal) &*&
               l_bound < u_bound &*& u_bound <= INT_MAX &*& 
               *i |-> _; @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               random_permission(principal, ?count2) &*&
               havege_util(pub, proof_pred, principal) &*&
               count2 > count1 &*& u_integer(i, ?val) &*& 
               l_bound <= val &*& val <= u_bound; @*/

#endif