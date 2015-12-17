#include "general.h"
#include "debug.h"
#include "item.h"
#include "key_item.h"
#include "principal_ids.h"
#include "invariants.h"

//@ import_module public_invariant_mod;
//@ import_module principal_ids;
//@ import_module nonce_item;
//@ import_module key_register;

///////////////////////////////////////////////////////////////////////////////
// Initialization/Finalization ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void init_crypto_lib()
  /*@ requires module(symbolic, true) &*&
               proof_obligations(?pub); @*/
  //@ ensures  world(pub) &*& principals_created(0);
{
  //@ open_module();
  //@ public_invariant_init(polarssl_pub(pub));
  nonces_init();
  //@ close exists(pub);
  key_registry_init();
  //@ close world(pub);
  principals_initialize();
}

void exit_crypto_lib()
  //@ requires world(?pub) &*& principals_created(_);
  //@ ensures  module(symbolic, false);
{
  //@ principals_finalize();
  //@ open world(pub);
  nonces_exit();
  key_registry_exit();
  //@ leak proof_obligations(pub);
  //@ close_module();
}



