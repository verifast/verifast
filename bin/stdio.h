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

fixpoint option<list<t> > option_cons<t>(t x, option<list<t> > xs) {
    switch (xs) {
        case none: return none;
        case some(xs0): return some(cons(x, xs0));
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
                                        case vararg_pointer(v): return option_cons(v, printf_parse_format(fcs1, args1));
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

/*@

inductive scanf_parse_mode = scanf_format | scanf_format_spec | scanf_scanset;

fixpoint option<list<pair<char, pair<void *, int> > > > scanf_parse_format(list<char> fcs, scanf_parse_mode mode, int width, list<vararg> args) {
    switch (fcs) {
        case nil: return mode == scanf_format ? some(nil) : none;
        case cons(fc0, fcs0): return
            mode == scanf_format ?
                fc0 != '%' ?
                    scanf_parse_format(fcs0, scanf_format, 0, args)
                :
                    scanf_parse_format(fcs0, scanf_format_spec, 0, args)
            : mode == scanf_scanset ?
                fc0 == '-' && (fcs0 == nil || head(fcs0) != ']') ? none :
                fc0 != ']' ? scanf_parse_format(fcs0, scanf_scanset, width, args) :
                    switch (args) {
                        case nil: return none;
                        case cons(arg0, args0): return
                            switch (arg0) {
                                case vararg_pointer(p): return option_cons(pair('s', pair(p, width)), scanf_parse_format(fcs0, scanf_format, 0, args0));
                                default: return none;
                            };
                    }
            :
                '0' <= fc0 && fc0 <= '9' ?
                    scanf_parse_format(fcs0, scanf_format_spec, width * 10 + fc0 - '0', args)
                : fc0 == 'i' || fc0 == 'd' ?
                    switch (args) {
                        case nil: return none;
                        case cons(arg0, args0): return
                            switch (arg0) {
                                case vararg_pointer(p): return option_cons(pair('i', pair(p, 0)), scanf_parse_format(fcs0, scanf_format, 0, args0));
                                default: return none;
                            };
                    }
                : fc0 == 's' ?
                    width == 0 ? none :
                    switch (args) {
                        case nil: return none;
                        case cons(arg0, args0): return
                            switch (arg0) {
                                case vararg_pointer(p): return option_cons(pair('s', pair(p, width)), scanf_parse_format(fcs0, scanf_format, 0, args0));
                                default: return none;
                            };
                    }
                : fc0 == '[' ?
                    width == 0 ? none :
                    switch (fcs0) {
                        case nil: return none;
                        case cons(fc1, fcs1): return
                            // Always skip first char, even if it's ']' or '-'.
                            fc1 == '^' ?
                                switch (fcs1) {
                                    case nil: return none;
                                    case cons(fc2, fcs2): return
                                        scanf_parse_format(fcs2, scanf_scanset, width, args);
                                }
                            :
                                scanf_parse_format(fcs1, scanf_scanset, width, args);
                    }
                : none;
    }
}

predicate scanf_targets(list<pair<char, pair<void *, int> > > targets, int fillCount;) =
    targets == nil ?
        emp
    :
        scanf_targets(tail(targets), fillCount - 1) &*&
        fst(head(targets)) == 'i' ?
            integer(fst(snd(head(targets))), _)
        :
            chars(fst(snd(head(targets))), snd(snd(head(targets))) + 1, ?cs) &*& fillCount <= 0 || mem('\0', cs) == true;

@*/

int scanf(char *format, ...);
    /*@
    requires // scanf_targets unrolled once to reduce reliance on auto-open/close
        [?f]string(format, ?fcs) &*& scanf_parse_format(fcs, scanf_format, 0, varargs) == some(?targets) &*&
        switch (targets) {
            case nil: return ensures [f]string(format, fcs);
            case cons(t0, ts0): return scanf_targets(ts0, 0) &*&
                fst(t0) == 'i' ?
                    integer(fst(snd(t0)), _) &*& ensures [f]string(format, fcs) &*& integer(fst(snd(t0)), _) &*& scanf_targets(ts0, result - 1)
                :
                    chars(fst(snd(t0)), snd(snd(t0)) + 1, _) &*& ensures[f]string(format, fcs) &*& chars(fst(snd(t0)), snd(snd(t0)) + 1, ?cs) &*& result < 1 || mem('\0', cs) &*& scanf_targets(ts0, result - 1);
        };
    @*/
    //@ ensures emp;

#endif