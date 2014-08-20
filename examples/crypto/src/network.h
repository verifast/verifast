#ifndef NETWORK_H
#define NETWORK_H

#include "item.h"
#include "general.h"

// see ../include/cryptolib.h

//@ predicate network_status_core(struct network_status *stat, bool initialized);

struct network_status *network_status_uninitialized();
  //@ requires true;
  //@ ensures  network_status_core(result, false);

struct network_status *network_bind(int port);
  //@ requires [?f0]world(?pub);
  //@ ensures  [f0]world(pub) &*& network_status_core(result, true);

void network_accept(struct network_status *stat);
  //@ requires [?f0]world(?pub) &*& network_status_core(stat, true);
  //@ ensures  [f0]world(pub) &*& network_status_core(stat, true);

struct item *network_receive_attempt(struct network_status *stat);
  //@ requires [?f0]world(?pub) &*& network_status(stat);
  /*@ ensures  [f0]world(pub) &*& network_status(stat) &*&
               result == 0 ? true : item(result, ?d) &*&
               (collision_in_run() || pub(d)); @*/

#endif
