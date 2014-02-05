#ifndef DLL_H
#define DLL_H

struct struct_dll;

//@ predicate predicate_dll(struct struct_dll* s);

void func();
  //@ requires true;
  //@ ensures  true;

struct struct_dll* get_struct_dll();
  //@ requires true;
  //@ ensures predicate_dll(result);

void free_struct_dll(struct struct_dll *s);
  //@ requires predicate_dll(s);
  //@ ensures true;

#endif
