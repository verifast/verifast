#ifndef SECURE_STORAGE_H
#define SECURE_STORAGE_H

// See explanations in ../../lib/include/dolevyao.h
#include "dolevyao.h"
#include "attacker.h"

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

fixpoint bool ss_pub(item i) {
  switch (i) {
    case key_item(p, c, k, info): 
      return bad(p);
    case data_item(d): return true;
    case hmac_item(creator, id, kind, info, m): 
      return bad(creator) || app_send_event(creator, m);
    case pair_item(i1, i2): return ss_pub(i1) && ss_pub(i2);
    case encrypted_item(s0, count0, kind0, info0, p0, entropy0):
      return ss_pub(p0) && bad(s0);
    default: return false;
  }
}
@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@ 
predicate protocol_pub(; fixpoint(item, bool) pub);

lemma void init_protocol();
     requires true;
     ensures protocol_pub(ss_pub);
@*/

void app_send(struct item *key, struct item *message);
  /*@ requires [?f0]world(ss_pub) &*& [?f1]net_api_initialized() &*&
                key_item(key, ?creator, ?id, symmetric_key, int_pair(0, 0)) &*& 
                item(message, ?msg) &*& ss_pub(msg) == true &*& 
                app_send_event(creator, msg) == true; 
  @*/
  /*@ ensures  [f0]world(ss_pub) &*& [f1]net_api_initialized() &*&
                key_item(key, creator, id, symmetric_key, int_pair(0, 0)) &*& 
                item(message, msg); 
  @*/

struct item *app_receive(struct item *key);
  /*@ requires [?f0]world(ss_pub) &*& [?f1]net_api_initialized() &*&
                key_item(key, ?creator, ?id, symmetric_key, int_pair(0, 0)); 
  @*/
  /*@ ensures [f0]world(ss_pub) &*& [f1]net_api_initialized() &*&
              key_item(key, creator, id, symmetric_key, int_pair(0, 0)) &*& 
              item(result, ?msg) &*& bad(creator) || 
              app_send_event(creator, msg); 
  @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ ATTACKER_PROOFS_DEFAULT(ss)

#endif