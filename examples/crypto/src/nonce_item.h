#ifndef NONCE_ITEM_H
#define NONCE_ITEM_H

#include "general.h"
#include "item.h"

// see ../include/cryptolib.h

//@ require_module nonce_item;

//@ predicate nonces_initialized();

void nonces_init();
  /*@ requires [?f]polarssl_world<item>(?pub) &*&
               module(nonce_item, true); @*/
  /*@ ensures  [f]polarssl_world<item>(pub) &*& 
               nonces_initialized(); @*/

void *nonces_expose_state();
  /*@ requires [?f1]polarssl_world<item>(?pub) &*&
               [?f2]nonces_initialized(); @*/
  /*@ ensures  [f1]polarssl_world<item>(pub) &*& 
               [f2]havege_state_initialized(result); @*/

void nonces_hide_state(void* state);
  /*@ requires [?f1]polarssl_world<item>(?pub) &*&
               [?f2]havege_state_initialized(state); @*/
  /*@ ensures  [f1]polarssl_world<item>(pub) &*& 
               [f2]nonces_initialized(); @*/

void nonces_exit();
  /*@ requires [?f]polarssl_world<item>(?pub) &*&
               nonces_initialized(); @*/
  /*@ ensures  [f]polarssl_world<item>(pub) &*&
               module(nonce_item, false); @*/

bool is_nonce(struct item *item);
  //@ requires item(item, ?i);
  /*@ ensures  item(item, i) &*&
        switch (i)
        {
          case data_item(d0):
            return result == false;
          case pair_item(f0, s0):
            return result == false;
          case nonce_item(p0, c0, inc0, i0):
            return result == true;
          case key_item(p0, c0, k0, i0):
            return result == false;
          case hmac_item(k0, pay0):
            return result == false;
          case encrypted_item(k0, pay0, ent0):
            return result == false;
        };
  @*/

void create_havege_random/*@ <T> @*/(char *output, int len);
  /*@ requires
        [?f0]world(?pub) &*& 
        nonce_request(?principal, ?info) &*&
        generated_values(principal, ?count) &*&
        chars(output, len, _);
  @*/
  /*@ ensures
        [f0]world(pub) &*& 
        generated_values(principal, count + 1) &*&
        polarssl_item(output, ?i) &*& 
        i == polarssl_havege_item(principal, count + 1) &*&
        len == length(havege_chars_for_polarssl_item(i)) &*&
        info == info_for_polarssl_item(i);
  @*/

#endif
