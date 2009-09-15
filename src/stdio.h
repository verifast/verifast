#ifndef STDIO_H
#define STDIO_H

struct file;

//@ predicate file(struct file* fp);

struct file* fopen(char* filename, char* mode); // todo: check that mode is a valid mode string
  /*@ requires [?f]chars(filename, ?fcs) &*& [?g]chars(mode, ?mcs) &*& chars_contains(fcs, 0) == true &*& chars_contains(mcs, 0) == true &*&
               (chars_length(mcs) == 2 || chars_length(mcs) == 3) &*&
               (char_at(mcs, 0) == 'r' || char_at(mcs, 0) == 'w' || char_at(mcs, 0) == 'a') &*&
               (chars_length(mcs) == 3 ? char_at(mcs, 1) == '+' : true);         
  @*/          
  //@ ensures [f]chars(filename, fcs) &*& [g]chars(mode, mcs) &*& result == 0 ? true : file(result);
  
int fread(void* buffer, int size, int n, struct file* fp);
  //@ requires chars(buffer, ?cs) &*& 0<=size &*& 0<=n &*& size * n <= chars_length(cs) &*& file(fp);
  //@ ensures chars(buffer, ?cs2) &*& chars_length(cs2) == chars_length(cs) &*& file(fp) &*& result <= n;
  
int fwrite(void* buffer, int size, int n, struct file* fp);
  //@ requires chars(buffer, ?cs) &*& 0<=size &*& 0<=n &*& size * n <= chars_length(cs) &*& file(fp);
  //@ ensures chars(buffer, cs) &*& file(fp);
  
char* fgets(char* buffer, int n, struct file* fp);
  //@ requires chars(buffer, ?cs) &*& chars_length(cs) == n &*& file(fp);
  //@ ensures chars(buffer, ?cs2) &*& chars_length(cs2) == n &*& file(fp) &*& result == 0 ? true : chars_contains(cs2, 0) == true;

int puts(char* format);
  //@ requires [?f]chars(format, ?cs) &*& chars_contains(cs, 0) == true;
  //@ ensures [f]chars(format, cs);
  
int printf(char* format, int arg);
  //@ requires [?f]chars(format, ?cs) &*& cs == chars_cons('%', chars_cons('i', chars_cons(0, chars_nil)));
  //@ ensures [f]chars(format, cs);

struct file* fclose(struct file* fp); 
  //@ requires file(fp);
  //@ ensures true;

#endif