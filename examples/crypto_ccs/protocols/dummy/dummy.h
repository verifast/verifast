#ifndef RPC_H
#define RPC_H

#include "../../annotated_api/polarssl_definitions/polarssl_definitions.h"

#define PACKAGE_SIZE 40

// 1. sender -> receiver : M

/*@

predicate dummy_proof_pred() = true;

fixpoint bool dummy_public_key(int p, int c, bool symmetric)
{
  return true == bad(p);
}

predicate dummy_pub(cryptogram cg) =
  switch (cg)
  {
    case cg_nonce(p0, c0):
      return true;
    case cg_symmetric_key(p0, c0): 
      return true == dummy_public_key(p0, c0, true);
    case cg_public_key(p0, c0):    
      return true;
    case cg_private_key(p0, c0):
      return true == dummy_public_key(p0, c0, false);
    case cg_hash(ccs0):             
      return true;
    case cg_hmac(p0, c0, ccs0):     
      return true == dummy_public_key(p0, c0, true);
    case cg_encrypted(p0, c0, ccs0, ent0):
      return true == dummy_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_auth_encrypted(p0, c0, ccs0, ent0):
      return true == dummy_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_asym_encrypted(p0, c0, ccs0, ent0):
      return [_]public_ccs(ccs0);
    case cg_asym_signature(p0, c0, ccs0, ent0):
      return true == dummy_public_key(p0, c0, false);
  }
;

@*/

void sender(char* msg);
  /*@ requires principal(?sender, _) &*&
               [?f]chars(msg, PACKAGE_SIZE, ?cs); @*/
  /*@ ensures  principal(sender, _) &*&
               [f]chars(msg, PACKAGE_SIZE, cs); @*/

void receiver(char* msg);
  /*@ requires principal(?receiver, _) &*&
               chars(msg, PACKAGE_SIZE, _); @*/
  /*@ ensures  principal(receiver, _) &*&
               chars(msg, PACKAGE_SIZE, ?cs); @*/

//@ PUBLIC_INVARIANT_PROOFS(dummy)
//@ DECRYPTION_PROOFS(dummy)

#endif
