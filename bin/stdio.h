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

/*@

fixpoint option<list<char *> > printf_cons(char *p, option<list<char *> > ps) {
    switch (ps) {
        case none: return none;
        case some(ps0): return some(cons(p, ps0));
    }
}

fixpoint option<list<char *> > printf_parse_format(list<char> fcs, list<vararg> args) {
    switch (fcs) {
        case nil: return some(nil);
        case cons(fc, fcs0): return
            fc != '%' ?
                printf_parse_format(fcs0, args)
            :
                switch (fcs0) {
                    case nil: return none;
                    case cons(fc1, fcs1): return
                        fc1 == '%' ?
                            printf_parse_format(fcs1, args)
                        : fc1 == 'd' || fc1 == 'i' || fc1 == 'c' ?
                            switch (args) {
                                case nil: return none;
                                case cons(arg, args1): return
                                    switch (arg) {
                                        case vararg_int(v): return printf_parse_format(fcs1, args1);
                                        default: return none;
                                    };
                            }
                        : fc1 == 'u' || fc1 == 'o' || fc1 == 'x' || fc1 == 'X' ?
                            switch (args) {
                                case nil: return none;
                                case cons(arg, args1): return
                                    switch (arg) {
                                        case vararg_uint(v): return printf_parse_format(fcs1, args1);
                                        default: return none;
                                    };
                            }
                        : fc1 == 'p' ?
                            switch (args) {
                                case nil: return none;
                                case cons(arg, args1): return
                                    switch (arg) {
                                        case vararg_pointer(v): return printf_parse_format(fcs1, args1);
                                        default: return none;
                                    };
                            }
                        : fc1 == 's' ?
                            switch (args) {
                                case nil: return none;
                                case cons(arg, args1): return
                                    switch (arg) {
                                        case vararg_pointer(v): return printf_cons(v, printf_parse_format(fcs1, args1));
                                        default: return none;
                                    };
                            }
                        :
                            none;
                };
    }
}

@*/

int printf(char* format, ...);
    /*@
    requires
        [?f]string(format, ?fcs) &*& printf_parse_format(fcs, varargs) == some(?ps) &*&
        switch (ps) {
            case nil: return ensures [f]string(format, fcs);
            case cons(p0, ps0): return [?f0]string(p0, ?cs0) &*&
                switch (ps0) {
                    case nil: return ensures [f]string(format, fcs) &*& [f0]string(p0, cs0);
                    case cons(p1, ps1): return [?f1]string(p1, ?cs1) &*&
                        switch (ps1) {
                            case nil: return ensures [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1);
                            case cons(p2, ps2): return [?f2]string(p2, ?cs2) &*&
                                switch (ps2) {
                                    case nil: return ensures [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1) &*& [f2]string(p2, cs2);
                                    case cons(p3, ps3): return [?f3]string(p3, ?cs3) &*&
                                        switch (ps3) {
                                            case nil: return ensures [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1) &*& [f2]string(p2, cs2) &*& [f3]string(p3, cs3);
                                            case cons(p4, ps4): return false; // TODO: Support more string arguments...
                                        };
                                };
                        };
                };
        };
    @*/
    //@ ensures emp;

int scanf(char* format, int* arg);
    //@ requires [?f]string(format, ?cs) &*& cs == cons('%', cons('i', nil)) &*& integer(arg, _);
    //@ ensures [f]string(format, cs) &*& integer(arg, _);

#endif