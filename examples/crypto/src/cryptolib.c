#include "general.h"
#include "debug.h"
#include "item.h"
#include "key_item.h"
#include "principals.h"
#include "invariants.h"

//@ import_module principals;
//@ import_module nonce_item;
//@ import_module key_register;

///////////////////////////////////////////////////////////////////////////////
// Initialization/Finalization ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void init_crypto_lib()
  /*@ requires module(cryptolib, true) &*&
               proof_obligations(?pub); @*/
  //@ ensures  world(pub) &*& principals_created(0);
{
  //@ open_module();

  //@ close exists(polarssl_pub(pub));
  //@ polarssl_init();
  
  //@ assert polarssl_principals(?count);
  nonces_init();
  //@ close exists(pub);
  key_registry_init();
  
  //@ close world(pub);
  principals_init();
}

void exit_crypto_lib()
  //@ requires world(?pub) &*& principals_created(_);
  //@ ensures  module(cryptolib, false);
{
  //@ principals_exit();
  //@ open world(pub);

  //@ polarssl_exit();
  nonces_exit();
  key_registry_exit();
  
  //@ leak proof_obligations(pub);
  //@ close_module();
}



