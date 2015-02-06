#ifndef SECURE_STORAGE_AUTH_H
#define SECURE_STORAGE_AUTH_H

#include "../../include/cryptolib.h"

/*@
fixpoint bool app_send_event(int sender, item message);

predicate ss_auth_pub(item i) =
  collision_in_run() ? true :
  [_]info_for_item(i, ?info0) &*&
  switch (i) 
  {
    case data_item(d0):
      return true;
    case pair_item(f0, s0):
      return [_]ss_auth_pub(f0) &*& 
             [_]ss_auth_pub(s0);
    case nonce_item(p0, c0, inc0): 
      return true;
    case hash_item(pay0): return
      switch (pay0)
      {
        case some(pay1):
          return [_]ss_auth_pub(pay1);
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
          return [_]ss_auth_pub(pay1);
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
            [_]ss_auth_pub(pay1)
          ) :
          false;
        case none:
          return true;
      };
    case asymmetric_signature_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1):
          return bad(p0) ? 
              [_]ss_auth_pub(pay1) 
            :
              true == app_send_event(p0, pay1);
        case none:
          return true;
      };
  }
;
@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void app_send(struct item *KA_PRIVATE, struct item *message);
  /*@ requires [?f0]world(ss_auth_pub) &*&
               generated_values(?principal, ?count) &*&
               item(KA_PRIVATE, ?kap, ss_auth_pub) &*& 
                 kap == private_key_item(?sender, ?count_kap) &*&
               item(message, ?msg, ss_auth_pub) &*&
                 [_]ss_auth_pub(msg) &*& 
                 app_send_event(sender, msg) == true; @*/
  /*@ ensures  [f0]world(ss_auth_pub) &*&
               generated_values(principal, count + 1) &*&
               item(KA_PRIVATE, kap, ss_auth_pub) &*& 
               item(message, msg, ss_auth_pub); @*/

struct item *app_receive(struct item *KA);
  /*@ requires [?f0]world(ss_auth_pub) &*&
               item(KA, ?ka, ss_auth_pub) &*&
                 ka == public_key_item(?sender, ?count_kap); @*/
  /*@ ensures  [f0]world(ss_auth_pub) &*&
               item(KA, ka, ss_auth_pub) &*&
               item(result, ?msg, ss_auth_pub) &*& 
               (
                 bad(sender) || 
                 collision_in_run() || 
                 app_send_event(sender, msg)
               ); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PROOFS_DEFAULT(ss_auth)

#endif
