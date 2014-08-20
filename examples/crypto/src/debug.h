#ifndef DEBUG_H
#define DEBUG_H

// see ../include/cryptolib.h

//@ require_module debug;

//@ predicate debug_initialized();

void debug_init();
  //@ requires module(debug, true);
  //@ ensures  debug_initialized();

void debug_exit();
  //@ requires debug_initialized();
  //@ ensures  module(debug, false);


#endif
