#ifndef DLL2_H
#define DLL2_H

struct struct_global
{
  int value;
};

struct struct_dll2;

//@ predicate predicate_dll2(struct struct_dll2* s);

struct struct_dll2* get_struct_dll2();
  //@ requires true;
  //@ ensures predicate_dll2(result);

void free_struct_dll2(struct struct_dll2 *s);
  //@ requires predicate_dll2(s);
  //@ ensures true;

#endif
