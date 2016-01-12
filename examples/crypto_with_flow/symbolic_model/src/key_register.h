#ifndef KEY_REGISTER_H
#define KEY_REGISTER_H

#include "general.h"

//@ require_module key_register;

//@ predicate key_registry_initialized(predicate(item) pub);

void key_registry_init();
  /*@ requires exists<predicate(item)>(?pub) &*&
               module(key_register, true); @*/
  //@ ensures  key_registry_initialized(pub);

void key_registry_exit();
  /*@ requires key_registry_initialized(_); @*/
  /*@ ensures  module(key_register, false); @*/

void register_public_key(int participant, struct item *key);
  /*@ requires world(?pub, ?key_clsfy) &*&
               item(key, public_key_item(participant, 1), pub); @*/
  /*@ ensures  world(pub, key_clsfy) &*&
               item(key, public_key_item(participant, 1), pub); @*/

#endif
