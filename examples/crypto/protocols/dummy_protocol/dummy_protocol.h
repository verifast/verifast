#ifndef DUMMY_PROTOCOL_H
#define DUMMY_PROTOCOL_H

#include "../../include/cryptolib.h"

/*@

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate dummy_pub(item i) =
  collision_in_run() ? true :
  [_]info_for_item(i, ?info0) &*&
  switch (i) 
  {
    case data_item(d0):
      return true;
    case pair_item(f0, s0):
      return [_]dummy_pub(f0) &*& 
             [_]dummy_pub(s0);
    case nonce_item(p0, c0, inc0): 
      return true == bad(p0);
    case hash_item(pay0): return
      switch (pay0)
      {
        case some(pay1):
          return [_]dummy_pub(pay1);
        case none:
          return true;
      };
    case symmetric_key_item(p0, c0):
      return true == bad(p0);
    case public_key_item(p0, c0):
      return true;
    case private_key_item(p0, c0):
      return true == bad(p0);
    case hmac_item(p0, c0, pay0): 
      return true;
    case symmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1):
          return [_]dummy_pub(pay1);
        case none:
          return true;
      };
    case asymmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1): return
          [_]message_tag(i)(?tag) &*& 
          tag == 10 ?
          (
            [_]dummy_pub(pay1)
          ) :
          false;
        case none:
          return true;
      };
    case asymmetric_signature_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1):
          return [_]dummy_pub(pay1);
        case none:
          return true;
      };
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void send();
  //@ requires [?f0]world(dummy_pub); 
  //@ ensures  [f0]world(dummy_pub);

struct item *receive();
  //@ requires [?f0]world(dummy_pub); 
  /*@ ensures  [f0]world(dummy_pub) &*& item(result, ?msg, dummy_pub) &*& 
               msg == data_item(_); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PROOFS_DEFAULT(dummy)

#endif
