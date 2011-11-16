#ifndef STDIO_H
#define STDIO_H

struct file;

//@ predicate file(struct file* fp);

struct file* fopen(char* filename, char* mode); // todo: check that mode is a valid mode string
  /*@ requires [?f]chars(filename, ?fcs) &*& [?g]chars(mode, ?mcs) &*& mem('\0', fcs) == true &*& mem('\0', mcs) == true &*&
               (length(mcs) == 2 || length(mcs) == 3) &*&
               (nth(0, mcs) == 'r' || nth(0, mcs) == 'w' || nth(0, mcs) == 'a') &*&
               (length(mcs) == 3 ? nth(1, mcs) == '+' || nth(1, mcs) == 'b' : true);         
  @*/          
  //@ ensures [f]chars(filename, fcs) &*& [g]chars(mode, mcs) &*& result == 0 ? true : file(result);
  
int fread(void* buffer, int size, int n, struct file* fp);
  //@ requires chars(buffer, ?cs) &*& 0<=size &*& 0<=n &*& size * n <= length(cs) &*& file(fp); // TODO!
  //@ ensures chars(buffer, ?cs2) &*& length(cs2) == length(cs) &*& file(fp) &*& result <= n;
  
int fwrite(void* buffer, int size, int n, struct file* fp);
  //@ requires chars(buffer, ?cs) &*& 0<=size &*& 0<=n &*& size * n <= length(cs) &*& file(fp);
  //@ ensures chars(buffer, cs) &*& file(fp);
  
char* fgets(char* buffer, int n, struct file* fp);
  //@ requires chars(buffer, ?cs) &*& length(cs) == n &*& file(fp);
  //@ ensures chars(buffer, ?cs2) &*& length(cs2) == n &*& file(fp) &*& result == 0 ? true : mem('\0', cs2) == true;

int puts(char* format);
  //@ requires [?f]chars(format, ?cs) &*& mem('\0', cs) == true;
  //@ ensures [f]chars(format, cs);
  
int printf(char* format, int arg);
  //@ requires [?f]chars(format, ?cs) &*& cs == cons('%', cons('i', cons('\0', nil)));
  //@ ensures [f]chars(format, cs);
  
int feof(struct file* fp);
  //@ requires file(fp);
  //@ ensures file(fp);
  
struct file* fclose(struct file* fp); 
  //@ requires file(fp);
  //@ ensures true;

#endif