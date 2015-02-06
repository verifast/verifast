#ifndef NONCE_ITEM_H
#define NONCE_ITEM_H

#include "general.h"

//@ require_module nonce_item;

//@ predicate nonces_initialized();

void nonces_init();
  //@ requires module(nonce_item, true);
  //@ ensures  nonces_initialized();

void *nonces_expose_state();
  //@ requires [?f]nonces_initialized();
  //@ ensures  [f]havege_state_initialized(result);

void nonces_hide_state(void* state);
  //@ requires [?f]havege_state_initialized(state);
  //@ ensures  [f]nonces_initialized();

void nonces_exit();
  //@ requires nonces_initialized();
  //@ ensures  module(nonce_item, false);

void create_havege_random(char *output, int len);
  /*@ requires [?f]world(?pub) &*& 
               nonce_request(?principal, ?info) &*&
               generated_values(principal, ?count) &*&
               chars(output, len, _);  @*/
  /*@ ensures  [f]world(pub) &*& 
               generated_values(principal, count + 1) &*&
               polarssl_cryptogram(output, len, ?cs, ?cg) &*& 
               cg == polarssl_random(principal, count + 1) &*&
               info == polarssl_cryptogram_info(cg); @*/

#endif
