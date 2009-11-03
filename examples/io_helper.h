#ifndef IO_HELPER_H
#define IO_HELPER_H

int read_int();
  //@ requires true;
  //@ ensures true;
  
char *read_string();
  //@ requires true;
  //@ ensures chars(result, ?cs2);

#endif