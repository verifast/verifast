#ifndef RANDOM_H
#define RANDOM_H

#include <stddef.h>

//@ #include "principals.gh"
//@ #include "cryptogram.gh"

#define MIN_RANDOM_SIZE 4
#define MINIMAL_STRING_SIZE 10

/*@

predicate random_request(int principal, int info, bool key) = true;

predicate random_state_predicate(predicate(void *) state_pred) = true;

#define PRG_PRECONDITION(STATE_PRED, STATE) \
  [?f]STATE_PRED(STATE) &*& \
  random_request(?principal, ?info, ?key_request) &*& \
  random_permission(principal, ?count) &*& \
  chars_(output, len, _) &*& len >= MIN_RANDOM_SIZE
  
#define PRG_POSTCONDITION(STATE_PRED, STATE) \
  [f]STATE_PRED(STATE) &*& \
  random_permission(principal, count + 1) &*& \
  result == 0 ? \
    cryptogram(output, len, ?ccs, ?cg) &*& \
    info == cg_info(cg) &*& \
    key_request ? \
      cg == cg_symmetric_key(principal, count + 1) \
    : \
      cg == cg_nonce(principal, count + 1) \
  : \
    chars_(output, len, _)

@*/

typedef int random_function/*@(predicate(void *) state_pred)@*/
                              (void* state, char* output, size_t len);
  //@ requires PRG_PRECONDITION(state_pred, state);
  //@ ensures PRG_POSTCONDITION(state_pred, state);

#endif
