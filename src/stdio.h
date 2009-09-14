#ifndef STDIO_H
#define STDIO_H

struct file;

//@ predicate file(struct file* fp);

struct file* fopen(char* filename, char* mode); // todo: check that mode is a valid mode string
  //@ requires [?f]chars(filename, ?fcs) &*& [?g]chars(mode, ?mcs) &*& chars_contains(fcs, 0) == true &*& chars_contains(mcs, 0) == true;
  //@ ensures [f]chars(filename, fcs) &*& [g]chars(mode, mcs) &*& result == 0 ? true : file(result);
  
char* fgets(char* buffer, int n, struct file* fp);
  //@ requires chars(buffer, ?cs) &*& chars_length(cs) == n &*& file(fp);
  //@ ensures chars(buffer, ?cs2) &*& chars_length(cs2) == n &*& file(fp) &*& result == 0 ? true : chars_contains(cs2, 0) == true;

int printf(char* format); // todo: support varargs
  //@ requires [?f]chars(format, ?cs) &*& chars_contains(cs, 0) == true;
  //@ ensures [f]chars(format, cs);

struct file* fclose(struct file* fp); 
  //@ requires file(fp);
  //@ ensures true;

#endif