#ifndef SECURE_STORAGE_H
#define SECURE_STORAGE_H

#include "../../include/cryptolib.h"

/*

Dolev-Yao security verification of a simple secure storage protocol

*/

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
fixpoint bool app_send_event(int sender, item message);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate ss_pub(item i) =
  collision_in_run() ? true :
  [_]info_for_item(i, ?info0) &*&
  switch (i) 
  {
    case data_item(d0):
      return true;
    case pair_item(f0, s0):
      return [_]ss_pub(f0) &*& 
             [_]ss_pub(s0);
    case nonce_item(p0, c0, inc0): 
      return true == bad(p0);
    case hash_item(pay0): return
      switch (pay0)
      {
        case some(pay1):
          return [_]ss_pub(pay1);
        case none:
          return true;
      };
    case symmetric_key_item(p0, c0):
      return true == bad(p0);
    case public_key_item(p0, c0):
      return true;
    case private_key_item(p0, c0):
      return true == bad(p0);
    case hmac_item(p0, c0, pay0): return
      switch(pay0)
      {
        case some(pay1):
          return bad(p0) || app_send_event(p0, pay1);
        case none:
          return true;
      };
    case symmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch(pay0)
      {
        case some(pay1):
          return [_]ss_pub(pay1);
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
            [_]ss_pub(pay1)
          ) :
          false;
        case none:
          return true;
      };
    case asymmetric_signature_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1):
          return [_]ss_pub(pay1);
        case none:
          return true;
      };
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void app_send(struct item *key, struct item *message);
  /*@ requires [?f0]world(ss_pub) &*&
               item(key, symmetric_key_item(?creator, ?id), ss_pub) &*& 
               item(message, ?msg, ss_pub) &*& [_]ss_pub(msg) &*&
               app_send_event(creator, msg) == true;
  @*/
  /*@ ensures  [f0]world(ss_pub) &*&
               item(key, symmetric_key_item(creator, id), ss_pub) &*&
               item(message, msg, ss_pub);
  @*/

struct item *app_receive(struct item *key);
  /*@ requires [?f0]world(ss_pub) &*&
               item(key, symmetric_key_item(?creator, ?id), ss_pub);
  @*/
  /*@ ensures  [f0]world(ss_pub) &*&
               item(key, symmetric_key_item(creator, id), ss_pub) &*&
               item(result, ?msg, ss_pub) &*& 
               (
                 bad(creator) || 
                 collision_in_run() || 
                 app_send_event(creator, msg)
               );
  @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PROOFS_DEFAULT(ss)

#endif
