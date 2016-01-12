#ifndef NETWORK_H
#define NETWORK_H

#include "general.h"
#include "item.h"

/*@ predicate network_status_core(struct network_status *stat, 
                                  bool initialized); @*/

struct network_status *network_status_uninitialized();
  //@ requires true;
  //@ ensures  network_status_core(result, false);

struct network_status *network_bind(int port);
  //@ requires true;
  //@ ensures  network_status_core(result, true);

void network_accept(struct network_status *stat);
  //@ requires network_status_core(stat, true);
  //@ ensures  network_status_core(stat, true);

struct item *network_receive_attempt(struct network_status *stat);
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*& principal(?id, ?count) &*&
               network_status(stat) &*&
               proof_obligations(pub); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*& principal(id, count) &*&
               network_status(stat) &*&
               proof_obligations(pub) &*&
               result == 0 ? 
                 true 
               : 
                 item(result, ?d, pub) &*&
                 col ? true : [_]pub(d); @*/

#endif
