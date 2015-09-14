#ifndef HAVEGE_UTIL_H
#define HAVEGE_UTIL_H

#include "havege.h"

/*@

typedef lemma void principal_with_public_random(predicate(cryptogram) pub,
                                                predicate() proof_pred,
                                                int principal)
                                               (cryptogram random);
  requires  proof_pred() &*&
            [_]public_invar(pub) &*&
            random == cg_random(principal, _);
  ensures   proof_pred() &*&
            [_]pub(random);

predicate havege_util(predicate(cryptogram) pub, predicate() proof_pred, int principal)=
  is_principal_with_public_random(?proof, pub, proof_pred, principal) &*&
  proof_pred()
;

#define DEFAULT_HAVEGE_UTIL_INIT(PUB, PRED, PRINCIPAL) \
{ \
  lemma void principal_with_public_random(cryptogram random) \
    requires  random == cg_random(PRINCIPAL, _); \
    ensures   [_]PUB(random); \
  { \
    close PUB(random); \
    leak PUB(random); \
  } \
  produce_lemma_function_pointer_chunk(principal_with_public_random) : \
    principal_with_public_random(PUB, PRED, PRINCIPAL)(random_){call();} \
    {duplicate_lemma_function_pointer_chunk(principal_with_public_random); \
     duplicate_lemma_function_pointer_chunk(principal_with_public_random);}; \
  leak is_principal_with_public_random(_, PUB, PRED, PRINCIPAL); \
  close PRED(); \
  close havege_util(PUB, PRED, PRINCIPAL); \
}

#define DEFAULT_HAVEGE_UTIL_EXIT(PUB, PRED, PRINCIPAL) \
{ \
  open havege_util(PUB, PRED, PRINCIPAL); \
  leak is_principal_with_public_random(_, PUB, PRED, PRINCIPAL); \
  open PRED(); \
}

@*/

void r_int(struct havege_state* state, int* i);
  /*@ requires [_]public_invar(?pub) &*&
               [?f]havege_state_initialized(state) &*&
               principal(?principal, ?count) &*&
               havege_util(pub, ?proof_pred, principal) &*&
               integer(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               principal(principal, count + 1) &*&
               havege_util(pub, proof_pred, principal) &*&
               integer(i, _); @*/

void r_int_with_bounds(struct havege_state* state, int* i, 
                         int l_bound, int u_bound);
  /*@ requires [_]public_invar(?pub) &*&
               [?f]havege_state_initialized(state) &*&
               principal(?principal, ?count1) &*&
               havege_util(pub, ?proof_pred, principal) &*&
               0 <= l_bound &*& l_bound < u_bound &*& 
               integer(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               principal(principal, ?count2) &*&
               havege_util(pub, proof_pred, principal) &*&
               count2 > count1 &*& integer(i, ?val) &*& 
               l_bound <= val &*& val <= u_bound; @*/

void r_u_int(struct havege_state* state, unsigned int* i);
  /*@ requires [_]public_invar(?pub) &*&
               [?f]havege_state_initialized(state) &*&
               principal(?principal, ?count) &*&
               havege_util(pub, ?proof_pred, principal) &*&
               u_integer(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               principal(principal, count + 1) &*&
               havege_util(pub, proof_pred, principal) &*&
               u_integer(i, _); @*/

void r_u_int_with_bounds(struct havege_state* state, unsigned int* i, 
                         unsigned int l_bound, unsigned int u_bound);
  /*@ requires [_]public_invar(?pub) &*&
               [?f]havege_state_initialized(state) &*&
               principal(?principal, ?count1) &*&
               havege_util(pub, ?proof_pred, principal) &*&
               l_bound < u_bound &*& u_bound <= INT_MAX &*& 
               u_integer(i, _); @*/
  /*@ ensures  [f]havege_state_initialized(state) &*&
               principal(principal, ?count2) &*&
               havege_util(pub, proof_pred, principal) &*&
               count2 > count1 &*& u_integer(i, ?val) &*& 
               l_bound <= val &*& val <= u_bound; @*/

#endif