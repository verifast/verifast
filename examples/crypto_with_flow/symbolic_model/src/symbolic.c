#include "general.h"
#include "debug.h"
#include "item.h"
#include "key_item.h"
#include "principal_ids.h"
#include "invariants.h"

//@ import_module public_invariant_mod;
//@ import_module decryption_mod;
//@ import_module principal_ids;
//@ import_module nonce_item;
//@ import_module key_register;

///////////////////////////////////////////////////////////////////////////////
// Initialization/Finalization ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void init_crypto_lib()
  /*@ requires module(symbolic, true) &*&
               is_key_classifier(?f, ?pub, ?key_clsfy) &*&
               proof_obligations(pub); @*/
  //@ ensures  world(pub, key_clsfy) &*& principals_created(0);
{
  //@ open_module();
  //@ public_invariant_init(polarssl_pub(pub));
  nonces_init();
  //@ close exists(pub);
  key_registry_init();
  //@ decryption_init(key_clsfy);
  //@ close world(pub, key_clsfy);
  principals_initialize();
}

void exit_crypto_lib()
  //@ requires world(?pub, ?key_clsfy) &*& principals_created(_);
  //@ ensures  true;
{
  //@ principals_finalize();
  //@ open world(pub, key_clsfy);
  nonces_exit();
  key_registry_exit();
  //@ leak proof_obligations(pub);
  //@ leak is_key_classifier(_, _, _);
  //@ leak module(key_register, false);
  //@ leak module(nonce_item, false);
}



