#ifndef STDIO_H
#define STDIO_H

typedef struct file FILE;

struct file;

//@ predicate file(struct file* fp);

FILE* fopen(char* filename, char* mode); // todo: check that mode is a valid mode string
  /*@ requires [?f]string(filename, ?fcs) &*& [?g]string(mode, ?mcs) &*&
               (length(mcs) == 1 || length(mcs) == 2) &*&
               (nth(0, mcs) == 'r' || nth(0, mcs) == 'w' || nth(0, mcs) == 'a') &*&
               (length(mcs) == 2 ? nth(1, mcs) == '+' || nth(1, mcs) == 'b' : true);
  @*/
  //@ ensures [f]string(filename, fcs) &*& [g]string(mode, mcs) &*& result == 0 ? true : file(result);

int fread(void* buffer, int size, int n, FILE* fp);
  //@ requires chars(buffer, ?m, ?cs) &*& 0<=size &*& 0<=n &*& size * n <= m &*& file(fp); // TODO!
  //@ ensures chars(buffer, m, ?cs2) &*& file(fp) &*& result <= n;
  
int fwrite(void* buffer, int size, int n, FILE* fp);
  //@ requires chars(buffer, ?m, ?cs) &*& 0<=size &*& 0<=n &*& size * n <= m &*& file(fp);
  //@ ensures chars(buffer, m, cs) &*& file(fp);
  
char* fgets(char* buffer, int n, FILE* fp);
  //@ requires chars(buffer, n, ?cs) &*& file(fp);
  //@ ensures chars(buffer, n, ?cs2) &*& file(fp) &*& result == 0 ? true : mem('\0', cs2) == true;

int fseek (FILE* fp, /*long*/ int offset, int origin);
  //@ requires file(fp) &*& origin == 0 || origin == 1 || origin == 2;
  //@ ensures file(fp);
  
/* long */ int ftell(FILE* fp);
  //@ requires file(fp);
  //@ ensures file(fp);
  
void rewind(FILE* fp);
  //@ requires file(fp);
  //@ ensures file(fp);

int puts(char* format);
  //@ requires [?f]string(format, ?cs);
  //@ ensures [f]string(format, cs);
  
int printf(char* format, int arg);
  //@ requires [?f]string(format, ?cs) &*& cs == cons('%', cons('i', nil));
  //@ ensures [f]string(format, cs);
  
int scanf(char* format, int* arg);
  //@ requires [?f]string(format, ?cs) &*& cs == cons('%', cons('i', nil)) &*& integer(arg, _);
  //@ ensures [f]string(format, cs) &*& integer(arg, _);

int feof(FILE* fp);
  //@ requires file(fp);
  //@ ensures file(fp);

int fclose(FILE* fp); 
  //@ requires file(fp);
  //@ ensures true;

int getchar();
  //@ requires true;
  //@ ensures true;

void putchar(char c);
  //@ requires true;
  //@ ensures true;

#endif