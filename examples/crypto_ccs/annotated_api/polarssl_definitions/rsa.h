#ifndef RSA_H
#define RSA_H

#include "macro_defines.h"
#include "havege.h"
#include "pk.h"

int rsa_gen_key(void *ctx, void *f_rng, void *p_rng,
                unsigned int nbits, int exponent);
  /*@ requires rsa_key_request(?principal, ?info) &*&
               random_permission(principal, ?count) &*&
               pk_context_initialized2(?pk_context, ctx) &*&
               pk_context->pk_ctx |-> ctx &*&
               //random_state_predicate(?state_pred) &*&
               [_]is_random_function(f_rng, ?state_pred) &*&
               [?f]state_pred(p_rng) &*&
               nbits >= 1024 &*& nbits <= 8192 &*& exponent == 65537; @*/
  /*@ ensures  random_permission(principal, count + 1) &*&
               pk_context_with_keys(pk_context, principal,
                                    count + 1, nbits, info) &*&
               [f]state_pred(p_rng); @*/

#endif