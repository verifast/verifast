#ifndef DLL1_H
#define DLL1_H

#include "dll2.h"

struct struct_dll1;

//@ predicate predicate_dll1(struct struct_dll1* s);

struct struct_dll1* get_struct_dll1();
  //@ requires true;
  //@ ensures predicate_dll1(result);

void free_struct_dll1(struct struct_dll1 *s);
  //@ requires predicate_dll1(s);
  //@ ensures true;

struct struct_dll2* get_struct_dll2_stub();
  //@ requires true;
  //@ ensures predicate_dll2(result);

void free_struct_dll2_stub(struct struct_dll2 *s);
  //@ requires predicate_dll2(s);
  //@ ensures true;

#endif
