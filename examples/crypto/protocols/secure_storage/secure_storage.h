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

fixpoint bool ss_pub(item i) 
{
  switch (i) {
    case key_item(p, c, k, info):
      return bad(p);
    case data_item(d): return true;
    case hmac_item(key, m): return
      switch (key)
      {
       case key_item(creator, c, k, info):
         return bad(creator) || app_send_event(creator, m);
       default: return false;
      };
    case pair_item(i1, i2): return ss_pub(i1) && ss_pub(i2);
    case nonce_item(p, c, inc, info): 
      return bad(p);
    case encrypted_item(k0, p0, e0): return
      switch (k0) 
      {
        case key_item(creator1, count1, kind1, info1) : return
          (ss_pub(k0) && ss_pub(p0)) || collision_in_run();
        default: return true;
      };
    default: return false;
  }
}

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void app_send(struct item *key, struct item *message);
  /*@ requires [?f0]world(ss_pub) &*&
               item(key, key_item(?creator, ?id, 
                                  symmetric_key, int_pair(0, 0))) &*& 
               item(message, ?msg) &*& ss_pub(msg) == true &*&
               app_send_event(creator, msg) == true;
  @*/
  /*@ ensures  [f0]world(ss_pub) &*&
               item(key, key_item(creator, id, 
                                  symmetric_key, int_pair(0, 0))) &*&
               item(message, msg);
  @*/

struct item *app_receive(struct item *key);
  /*@ requires [?f0]world(ss_pub) &*&
               item(key, key_item(?creator, ?id, 
                                  symmetric_key, int_pair(0, 0)));
  @*/
  /*@ ensures  [f0]world(ss_pub) &*&
               item(key, key_item(creator, id, 
                                  symmetric_key, int_pair(0, 0))) &*&
               item(result, ?msg) &*& 
               (
                 bad(creator) || 
                 collision_in_run() || 
                 app_send_event(creator, msg)
               );
  @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ ATTACKER_PROOFS_DEFAULT(ss)

#endif
