#ifndef NONCE_ITEM_H
#define NONCE_ITEM_H

#include "general.h"

//@ require_module nonce_item;

//@ predicate nonces_initialized();
//@ predicate nonces_state(void *state);

void nonces_init();
  //@ requires module(nonce_item, true);
  //@ ensures  nonces_initialized();

void *nonces_expose_state();
  //@ requires [?f]nonces_initialized();
  //@ ensures  [f]havege_state_initialized(result) &*& [_]nonces_state(result);

void nonces_hide_state(void* state);
  //@ requires [?f]havege_state_initialized(state) &*& [_]nonces_state(state);
  //@ ensures  [f]nonces_initialized();

void nonces_exit();
  //@ requires nonces_initialized();
  //@ ensures  module(nonce_item, false);

void create_havege_random(char *output, int len);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& 
               nonce_request(?principal, ?info) &*&
               principal(principal, ?count) &*&
               chars_(output, len, _);  @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*& 
               principal(principal, count + 1) &*&
               cryptogram(output, len, ?cs, ?cg) &*& 
               cg == cg_nonce(principal, count + 1) &*&
               info == cg_info(cg); @*/

#endif
