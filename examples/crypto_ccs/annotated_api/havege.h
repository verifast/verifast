#ifndef HAVEGE_H
#define HAVEGE_H

#include <stdlib.h>
#include "crypto.h"
#include "macro_defines.h"

struct havege_state
{
  char content[HAVEGE_STATE_SIZE];
};
typedef struct havege_state havege_state;

/*@

predicate havege_state(havege_state *state) =
  chars_(state->content, HAVEGE_STATE_SIZE, _) &*&
  struct_havege_state_padding(state)
;

predicate havege_state_initialized(havege_state *state);

@*/

void havege_init(havege_state *havege_state);
  /*@ requires havege_state(havege_state); @*/
  /*@ ensures  havege_state_initialized(havege_state); @*/

void havege_free(havege_state *havege_state);
  //@ requires havege_state_initialized(havege_state);
  //@ ensures  havege_state(havege_state);

int havege_random(void *havege_state, char *output, size_t len);
  //@ requires PRG_PRECONDITION(havege_state_initialized, havege_state);
  //@ ensures PRG_POSTCONDITION(havege_state_initialized, havege_state);

#endif