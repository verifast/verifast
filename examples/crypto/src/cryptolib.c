#include "general.h"
#include "debug.h"
#include "item.h"
#include "nonce_item.h"
#include "key_item.h"
#include "principals.h"
#include "polarssl_invariants.h"

//@ import_module debug;
//@ import_module nonce_item;
//@ import_module key_item;
//@ import_module principals;

///////////////////////////////////////////////////////////////////////////////
// Initialization/Finalization ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void init_crypto_lib()
  /*@ requires  module(cryptolib, true) &*&
                exists<fixpoint(item, bool)>(?pub);
  @*/
  //@ ensures  world(pub) &*& initial_principals();
{
  //@ open_module();

  //@ open exists<fixpoint(item, bool)>(pub);
  //@ close exists<fixpoint(item i, list<char>, bool)>(polarssl_pub(pub));
  //@ polarssl_init<item>();
  nonces_init();
  debug_init();
  key_registry_init();
  //@ open polarssl_initial_principals();
  //@ assert polarssl_principals(?count);
  //@ close world(pub);
  principals_init();
}

void exit_crypto_lib()
  //@ requires world(?pub) &*& principals_created(_);
  //@ ensures  module(cryptolib, false);
{
  //@ principals_exit();  
  //@ open world(pub);
  
  nonces_exit();
  debug_exit();
  key_registry_exit();
  //@ polarssl_exit();

  //@ close_module();
}



