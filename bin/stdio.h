/**
 * Contracts for C standard library's input/output functions.
 *
 * If you are looking for contract supporting specifying input/output behaviour,
 * see io/stdio.h. These contracts are also closer to the actual API.
 */

#ifndef STDIO_H
#define STDIO_H

#include "stddef.h"
#include "stdarg.h"

#ifndef EOF
# define EOF (-1)
#endif

typedef struct file FILE;

struct file;

//@ predicate file(struct file* fp;);

FILE* __get_stdin();
    //@ requires true;
    //@ ensures [_]file(result);

#define stdin __get_stdin()

FILE* __get_stdout();
    //@ requires true;
    //@ ensures [_]file(result);

#define stdout __get_stdout()

FILE* __get_stderr();
    //@ requires true;
    //@ ensures [_]file(result);

#define stderr __get_stderr()

FILE* fopen(char* filename, char* mode); // todo: check that mode is a valid mode string
    /*@ requires [?f]string(filename, ?fcs) &*& [?g]string(mode, ?mcs) &*&
                 (length(mcs) == 1 || length(mcs) == 2) &*&
                 (nth(0, mcs) == 'r' || nth(0, mcs) == 'w' || nth(0, mcs) == 'a') &*&
                 (length(mcs) == 2 ? nth(1, mcs) == '+' || nth(1, mcs) == 'b' : true);
    @*/
    //@ ensures [f]string(filename, fcs) &*& [g]string(mode, mcs) &*& result == 0 ? true : file(result);

int fread(void* buffer, size_t size, size_t n, FILE* fp);
    //@ requires chars_(buffer, ?m, ?cs) &*& 0<=size &*& 0<=n &*& size * n <= m &*& [?f]file(fp);
    //@ ensures chars(buffer, size * result, ?cs2) &*& chars_(buffer + size * result, m - size * result, _) &*& [f]file(fp) &*& 0 <= result &*& result <= n;
  
int fwrite(void* buffer, size_t size, size_t n, FILE* fp);
    //@ requires [?fb]chars(buffer, ?m, ?cs) &*& 0<=size &*& 0<=n &*& size * n <= m &*& [?ff]file(fp);
    //@ ensures [fb]chars(buffer, m, cs) &*& [ff]file(fp) &*& 0 <= result &*& result <= n;
  
char* fgets(char* buffer, int n, FILE* fp);
    //@ requires chars_(buffer, n, ?cs) &*& [?f]file(fp);
    //@ ensures [f]file(fp) &*& result == 0 ? chars_(buffer, n, _) : string(buffer, ?scs) &*& buffer[length(scs) + 1..n] |-> _;

int fputs(char* s, FILE* fp);
    //@ requires [?fs]string(s, ?cs) &*& [?ff]file(fp);
    //@ ensures [fs]string(s, cs) &*& [ff]file(fp);

int fseek (FILE* fp, /*long*/ int offset, int origin);
    //@ requires [?f]file(fp) &*& origin == 0 || origin == 1 || origin == 2;
    //@ ensures [f]file(fp);
  
long ftell(FILE* fp);
    //@ requires [?f]file(fp);
    //@ ensures [f]file(fp);
  
void rewind(FILE* fp);
    //@ requires [?f]file(fp);
    //@ ensures [f]file(fp);

int puts(char* text);
    //@ requires [?f]string(text, ?cs);
    //@ ensures [f]string(text, cs);

int fgetc(FILE* fp);
    //@ requires [?f]file(fp);
    //@ ensures [f]file(fp) &*& result == EOF || 0 <= result && result <= 255;
  
int feof(FILE* fp);
    //@ requires [?f]file(fp);
    //@ ensures [f]file(fp);

int fflush(FILE* fp);
    //@ requires [?f]file(fp);
    //@ ensures [f]file(fp);

int fclose(FILE* fp); 
    //@ requires file(fp);
    //@ ensures true;

int getchar();
    //@ requires true;
    //@ ensures true;

int putchar(char c);
    //@ requires true;
    //@ ensures c == result || EOF == result;

void setbuf(FILE* fp, char* buffer);
    //@ requires [?f]file(fp) &*& buffer == 0;
    //@ ensures [f]file(fp);

/*@

fixpoint list<list<char> > printf_tokenize_format(bool inSpec, list<char> cs) {
    switch (cs) {
        case nil: return inSpec ? {nil} : nil;
        case cons(c, cs0): return
            inSpec ?
                mem(c, {'-', '+', '#', ' ', '.', '*', 'h', 'l', 'j', 'z', 't', 'L'}) || '0' <= c && c <= '9' ?
                    cons(cons(c, head(printf_tokenize_format(true, cs0))), tail(printf_tokenize_format(true, cs0)))
                :
                    cons({c}, printf_tokenize_format(false, cs0))
            :
                c == '%' ?
                    printf_tokenize_format(true, cs0)
                :
                    printf_tokenize_format(false, cs0);
    }
}

fixpoint option<pair<list<char *>, list<vararg> > > printf_parse_specifier(list<char> cs, list<vararg> args) {
    switch (cs) {
        case nil: return none;
        case cons(c, cs0): return
            switch (args) {
                case nil: return none;
                case cons(arg, args0): return
                    c == 'd' || c == 'i' || c == 'c' ?
                        switch (arg) {
                            case vararg_int(size, v): return size == sizeof(int) ? some(pair({}, args0)) : none;
                            default: return none;
                        }
                    : c == 'u' || c == 'o' || c == 'x' || c == 'X' ?
                        switch (arg) {
                            case vararg_uint(size, v): return size == sizeof(unsigned int) ? some(pair({}, args0)) : none;
                            default: return none;
                        }
                    : c == 'p' ?
                        switch (arg) {
                            case vararg_pointer(v): return some(pair({}, args0));
                            default: return none;
                        }
                    : mem(c, {'f', 'F', 'e', 'E', 'g', 'G', 'a', 'A'}) ?
                        switch (arg) {
                            case vararg_double(d): return some(pair({}, args0));
                            default: return none;
                        }
                    : c == 's' ?
                        switch (arg) {
                            case vararg_pointer(v): return some(pair({v}, args0));
                            default: return none;
                        }
                    : c == 'l' ?
                        switch (cs0) {
                            case nil: return none;
                            case cons(c1, cs1): return
                                c1 == 'd' || c1 == 'i' ?
                                    switch (arg) {
                                        case vararg_int(size, v): return size == sizeof(long) ? some(pair({}, args0)) : none;
                                        default: return none;
                                    }
                                : c1 == 'u' || c1 == 'o' || c1 == 'x' || c1 == 'X' ?
                                    switch (arg) {
                                        case vararg_uint(size, v): return size == sizeof(unsigned long) ? some(pair({}, args0)) : none;
                                        default: return none;
                                    }
                                : c == 'l' ?
                                    switch (cs1) {
                                        case nil: return none;
                                        case cons(c2, cs2): return
                                            c2 == 'd' || c2 == 'i' ?
                                                switch (arg) {
                                                    case vararg_int(size, v): return size == sizeof(long long) ? some(pair({}, args0)) : none;
                                                    default: return none;
                                                }
                                            : c2 == 'u' || c2 == 'o' || c2 == 'x' || c2 == 'X' ?
                                                switch (arg) {
                                                    case vararg_uint(size, v): return size == sizeof(unsigned long long) ? some(pair({}, args0)) : none;
                                                    default: return none;
                                                }
                                            :
                                                none;
                                    }
                                :
                                    none;
                        }
                    :
                        none;
            };
    }
}

fixpoint option<pair<list<char *>, list<vararg> > > printf_parse_precision_digits(list<char> cs, list<vararg> args) {
    switch (cs) {
        case nil: return none;
        case cons(c, cs0): return
            '0' <= c && c <= '9' ?
                printf_parse_precision_digits(cs0, args)
            :
                printf_parse_specifier(cs, args);
    }
}

fixpoint option<pair<list<char *>, list<vararg> > > printf_parse_precision(list<char> cs, list<vararg> args) {
    switch (cs) {
        case nil: return none;
        case cons(c, cs0): return
            c == '.' ?
                switch (cs0) {
                    case nil: return none;
                    case cons(c0, cs00): return
                        c0 == '*' ?
                            switch (args) {
                                case nil: return none;
                                case cons(arg, args0): return
                                    switch (arg) {
                                        case vararg_int(size, v): return size == sizeof(int) ? printf_parse_specifier(cs00, args0) : none;
                                        default: return none;
                                    };
                            }
                        :
                            printf_parse_precision_digits(cs0, args);
                }
            :
                printf_parse_specifier(cs, args);
    }
}

fixpoint option<pair<list<char *>, list<vararg> > > printf_parse_width_digits(list<char> cs, list<vararg> args) {
    switch (cs) {
        case nil: return none;
        case cons(c, cs0): return
            '0' <= c && c <= '9' ?
                printf_parse_width_digits(cs0, args)
            :
                printf_parse_precision(cs, args);
    }
}

fixpoint option<pair<list<char *>, list<vararg> > > printf_parse_flags(list<char> cs, list<vararg> args) {
    switch (cs) {
        case nil: return none;
        case cons(c, cs0): return
            c == '-' || c == '+' || c == ' ' || c == '#' || c == '0' ?
                printf_parse_flags(cs0, args)
            : c == '*' ?
                switch (args) {
                    case nil: return none;
                    case cons(arg, args0): return
                        switch (arg) {
                            case vararg_int(size, v): return size == sizeof(int) ? printf_parse_precision(cs0, args0) : none;
                            default: return none;
                        };
                }
            :
                printf_parse_width_digits(cs, args);
    }
}

fixpoint option<list<char *> > printf_parse_specs(list<list<char> > specs, list<vararg> args) {
    switch (specs) {
        case nil: return some(nil);
        case cons(spec, specs0): return
            switch (printf_parse_flags(spec, args)) {
                case none: return none;
                case some(result): return
                    switch (result) {
                        case pair(ss0, args_rest): return
                            switch (printf_parse_specs(specs0, args_rest)) {
                                case none: return none;
                                case some(ss1): return some(append(ss0, ss1));
                            };
                    };
            };
    }
}

fixpoint option<list<char *> > printf_parse_format(list<char> cs, list<vararg> args) {
    return printf_parse_specs(printf_tokenize_format(false, cs), args);
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

int snprintf(char *buffer, size_t count, char* format, ...);
    /*@
    requires
        buffer[..count] |-> _ &*& 0 < count &*& [?f]string(format, ?fcs) &*& printf_parse_format(fcs, varargs) == some(?ps) &*&
        switch (ps) {
            case nil: return ensures buffer[..count] |-> ?cs &*& mem('\0', cs) == true &*& [f]string(format, fcs);
            case cons(p0, ps0): return [?f0]string(p0, ?cs0) &*&
                switch (ps0) {
                    case nil: return ensures buffer[..count] |-> ?cs &*& mem('\0', cs) == true &*& [f]string(format, fcs) &*& [f0]string(p0, cs0);
                    case cons(p1, ps1): return [?f1]string(p1, ?cs1) &*&
                        switch (ps1) {
                            case nil: return ensures buffer[..count] |-> ?cs &*& mem('\0', cs) == true &*& [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1);
                            case cons(p2, ps2): return [?f2]string(p2, ?cs2) &*&
                                switch (ps2) {
                                    case nil: return ensures buffer[..count] |-> ?cs &*& mem('\0', cs) == true &*& [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1) &*& [f2]string(p2, cs2);
                                    case cons(p3, ps3): return [?f3]string(p3, ?cs3) &*&
                                        switch (ps3) {
                                            case nil: return ensures buffer[..count] |-> ?cs &*& mem('\0', cs) == true &*& [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1) &*& [f2]string(p2, cs2) &*& [f3]string(p3, cs3);
                                            case cons(p4, ps4): return false; // TODO: Support more string arguments...
                                        };
                                };
                        };
                };
        };
    @*/
    //@ ensures emp;

int fprintf(FILE *file, char* format, ...);
    /*@
    requires
        [?ff]file(file) &*& [?f]string(format, ?fcs) &*& printf_parse_format(fcs, varargs) == some(?ps) &*&
        switch (ps) {
            case nil: return ensures [ff]file(file) &*& [f]string(format, fcs);
            case cons(p0, ps0): return [?f0]string(p0, ?cs0) &*&
                switch (ps0) {
                    case nil: return ensures [ff]file(file) &*& [f]string(format, fcs) &*& [f0]string(p0, cs0);
                    case cons(p1, ps1): return [?f1]string(p1, ?cs1) &*&
                        switch (ps1) {
                            case nil: return ensures [ff]file(file) &*& [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1);
                            case cons(p2, ps2): return [?f2]string(p2, ?cs2) &*&
                                switch (ps2) {
                                    case nil: return ensures [ff]file(file) &*& [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1) &*& [f2]string(p2, cs2);
                                    case cons(p3, ps3): return [?f3]string(p3, ?cs3) &*&
                                        switch (ps3) {
                                            case nil: return ensures [ff]file(file) &*& [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1) &*& [f2]string(p2, cs2) &*& [f3]string(p3, cs3);
                                            case cons(p4, ps4): return false; // TODO: Support more string arguments...
                                        };
                                };
                        };
                };
        };
    @*/
    //@ ensures emp;

int vfprintf(FILE *file, char* format, va_list ap);
    /*@
    requires
        [?ff]file(file) &*& [?f]string(format, ?fcs) &*& va_list(ap, ?lastParam, ?apFrac, ?args) &*& printf_parse_format(fcs, args) == some(?ps) &*&
        switch (ps) {
            case nil: return ensures [ff]file(file) &*& [f]string(format, fcs) &*& va_list(?ap1, lastParam, apFrac, _) &*& va_list_id(ap1) == va_list_id(ap);
            case cons(p0, ps0): return [?f0]string(p0, ?cs0) &*&
                switch (ps0) {
                    case nil: return ensures [ff]file(file) &*& [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& va_list(?ap1, lastParam, apFrac, _) &*& va_list_id(ap1) == va_list_id(ap);
                    case cons(p1, ps1): return [?f1]string(p1, ?cs1) &*&
                        switch (ps1) {
                            case nil: return ensures [ff]file(file) &*& [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1) &*& va_list(?ap1, lastParam, apFrac, _) &*& va_list_id(ap1) == va_list_id(ap);
                            case cons(p2, ps2): return [?f2]string(p2, ?cs2) &*&
                                switch (ps2) {
                                    case nil: return ensures [ff]file(file) &*& [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1) &*& [f2]string(p2, cs2) &*& va_list(?ap1, lastParam, apFrac, _) &*& va_list_id(ap1) == va_list_id(ap);
                                    case cons(p3, ps3): return [?f3]string(p3, ?cs3) &*&
                                        switch (ps3) {
                                            case nil: return ensures [ff]file(file) &*& [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1) &*& [f2]string(p2, cs2) &*& [f3]string(p3, cs3) &*& va_list(?ap1, lastParam, apFrac, _) &*& va_list_id(ap1) == va_list_id(ap);
                                            case cons(p4, ps4): return false; // TODO: Support more string arguments...
                                        };
                                };
                        };
                };
        };
    @*/
    //@ ensures emp;

/*@

inductive format_part =
  format_part_char(char) |
  format_part_int_specifier(int) |
  format_part_uint_specifier(unsigned int) |
  format_part_string_specifier(char*);

fixpoint option<list<t> > option_cons<t>(t x, option<list<t> > xs) {
    switch (xs) {
        case none: return none;
        case some(xs0): return some(cons(x, xs0));
    }
}

fixpoint int option_length<t>(option<list<t> > xs) {
    switch (xs) {
        case none: return 0;
        case some(xs0): return
            switch (xs0) {
                case nil: return 0;
                case cons(x, xs1): return 1 + length(xs1);
            };
    }
}

fixpoint option<list<t> > option_append<t>(list<t> xs0, option<list<t> > xs1) {
    switch (xs1) {
        case none: return none;
        case some(xs2): return some(append(xs0, xs2));
    }
}

fixpoint option<list<t> > option_option_append<t>(option<list<t> > xs0, option<list<t> > xs1) {
    switch (xs0) {
        case none: return none;
        case some(xs0'): return 
            switch (xs1) {
                case none: return none;
                case some(xs1'): return some(append(xs0', xs1'));
            };
    }
}

fixpoint option<list<format_part> > sprintf_parse_format(list<char> fcs, list<vararg> args) {
    switch (fcs) {
        case nil: return some(nil);
        case cons(fc, fcs0): return
            fc != '%' ?
                option_cons(format_part_char(fc), sprintf_parse_format(fcs0, args))
            :
                switch (fcs0) {
                    case nil: return none;
                    case cons(fc1, fcs1): return
                        fc1 == '%' ?
                            option_cons(format_part_char('%'),
                              sprintf_parse_format(fcs1, args))
                        : fc1 == 'd' || fc1 == 'i' || fc1 == 'c' ?
                            switch (args) {
                                case nil: return none;
                                case cons(arg, args1): return
                                    switch (arg) {
                                        case vararg_int(size, v): return
                                           size == sizeof(int) ?
                                               option_cons(format_part_int_specifier(v), sprintf_parse_format(fcs1, args1))
                                           :
                                               none;
                                        default: return none;
                                    };
                            }
                        : fc1 == 'u' ?
                            switch (args) {
                                case nil: return none;
                                case cons(arg, args1): return
                                    switch (arg) {
                                        case vararg_uint(size, v): return
                                            size == sizeof(unsigned int) ?
                                                option_cons(format_part_uint_specifier(v), sprintf_parse_format(fcs1, args1))
                                            :
                                                none;
                                        default: return none;
                                    };
                            }
                        : fc1 == 's' ?
                            switch (args) {
                                case nil: return none;
                                case cons(arg, args1): return
                                    switch (arg) {
                                        case vararg_pointer(v): return 
                                          option_cons(format_part_string_specifier(v), sprintf_parse_format(fcs1, args1));
                                        default: return none;
                                    };
                            }
                        :
                            none;
                };
    }
}

fixpoint option<list<char> > chars_for_uint(int i) {
    return i > 9 || i < 0 ? none : some(cons(i + 48, nil));
}

fixpoint option<list<char> > chars_for_int(int i) {
    return i > 9 || i < -9 ? none :
               i < 0 ? option_cons('-', chars_for_uint(-i)) : chars_for_uint(i);
}

fixpoint option<list<char> > sprintf_filled_in_args(list<format_part> parts, list<list<char> > string_args) {
    switch (parts) {
        case nil: return some(cons(0, nil));
        case cons(arg0, args0): return
            switch (arg0) {
                case format_part_char(c):
                    return option_cons(c, sprintf_filled_in_args(args0, string_args));
                case format_part_int_specifier(i): 
                    return option_option_append(chars_for_int(i), sprintf_filled_in_args(args0, string_args));
                case format_part_uint_specifier(i):
                    return option_option_append(chars_for_uint(i), sprintf_filled_in_args(args0, string_args));
                case format_part_string_specifier(s): return
                    switch(string_args) {
                        case cons(cs, string_args0):
                            return option_append(cs, sprintf_filled_in_args(args0, string_args0));
                        case nil: return none;
                    };
            };
    }
}

@*/

int sprintf(char* dest, char* format, ...);
    /*@ 
    requires [?f]string(format, ?f_cs) &*&
             chars_(dest, ?d_length, _) &*&
             sprintf_parse_format(f_cs, varargs) == some(?parsed_format) &*&
             // string chunck requirements
             printf_parse_format(f_cs, varargs) == some(?ps) &*&
             switch (ps) {
                case nil: 
                    return 
                        sprintf_filled_in_args(parsed_format, {}) == some(?r_cs) &*&
                        d_length >= length(r_cs) &*& 
                    ensures
                        [f]string(format, f_cs) &*&
                        chars(dest, length(r_cs), r_cs) &*&
                        chars_(dest + length(r_cs), d_length - length(r_cs), _);
                case cons(p0, ps0): return [?f0]string(p0, ?cs0) &*&
                    switch (ps0) {
                        case nil: 
                            return 
                                sprintf_filled_in_args(parsed_format, {cs0}) == some(?r_cs) &*&
                                d_length >= length(r_cs) &*& 
                            ensures 
                                [f0]string(p0, cs0) &*&
                                [f]string(format, f_cs) &*&  
                                chars(dest, length(r_cs), r_cs) &*&
                                chars_(dest + length(r_cs), d_length - length(r_cs), _);
                        case cons(p1, ps1): return [?f1]string(p1, ?cs1) &*&
                            switch (ps1) {
                                case nil: 
                                    return 
                                        sprintf_filled_in_args(parsed_format, {cs0, cs1}) == some(?r_cs) &*&
                                        d_length >= length(r_cs) &*& 
                                    ensures
                                        [f1]string(p1, cs1) &*&
                                        [f0]string(p0, cs0) &*&
                                        [f]string(format, f_cs) &*&  
                                        chars(dest, length(r_cs), r_cs) &*&
                                        chars_(dest + length(r_cs), d_length - length(r_cs), _);
                                case cons(p2, ps2): return [?f2]string(p2, ?cs2) &*&
                                    switch (ps2) {
                                        case nil: 
                                            return 
                                                sprintf_filled_in_args(parsed_format, {cs0, cs1, cs2}) == some(?r_cs) &*&
                                                d_length >= length(r_cs) &*& 
                                            ensures
                                                [f2]string(p2, cs2) &*&
                                                [f1]string(p1, cs1) &*&
                                                [f0]string(p0, cs0) &*&
                                                [f]string(format, f_cs) &*&  
                                                chars(dest, length(r_cs), r_cs) &*&
                                                chars_(dest + length(r_cs), d_length - length(r_cs), _);
                                        case cons(p3, ps3): return [?f3]string(p3, ?cs3) &*&
                                            switch (ps3) {
                                                case nil: 
                                                    return 
                                                        sprintf_filled_in_args(parsed_format, {cs0, cs1, cs2, cs3}) == some(?r_cs) &*&
                                                        d_length >= length(r_cs) &*&       
                                                    ensures
                                                        [f3]string(p3, cs3) &*&
                                                        [f2]string(p2, cs2) &*&
                                                        [f1]string(p1, cs1) &*&
                                                        [f0]string(p0, cs0) &*&
                                                        [f]string(format, f_cs) &*&  
                                                        chars(dest, length(r_cs), r_cs) &*&
                                                        chars_(dest + length(r_cs), d_length - length(r_cs), _);
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
                fc0 == '0' || fc0 == '1' || fc0 == '2' || fc0 == '3' || fc0 == '4' || fc0 == '5' || fc0 == '6' || fc0 == '7' || fc0 == '8' || fc0 == '9' ?
                    width == 0 && fc0 == '0' ? none : scanf_parse_format(fcs0, scanf_format_spec, width * 10 + fc0 - '0', args)
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
                : fc0 == 'c' ?
                    switch (args) {
                        case nil: return none;
                        case cons(arg0, args0): return
                            switch (arg0) {
                                case vararg_pointer(p): return option_cons(pair('c', pair(p, width == 0 ? 1 : width)), scanf_parse_format(fcs0, scanf_format, 0, args0));
                                default: return none;
                            };
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
        : fst(head(targets)) == 'c' ?
            chars(fst(snd(head(targets))), snd(snd(head(targets))), _)
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
                    int_(fst(snd(t0)), _) &*& ensures [f]string(format, fcs) &*& integer(fst(snd(t0)), _) &*& scanf_targets(ts0, result - 1)
                :
                    chars_(fst(snd(t0)), snd(snd(t0)) + 1, _) &*& ensures[f]string(format, fcs) &*& chars(fst(snd(t0)), snd(snd(t0)) + 1, ?cs) &*& result < 1 || mem('\0', cs) &*& scanf_targets(ts0, result - 1);
        };
    @*/
    //@ ensures emp;

int sscanf(char *s, char *format, ...);
    /*@
    requires // scanf_targets unrolled once to reduce reliance on auto-open/close
        [?fs]string(s, ?scs) &*& [?f]string(format, ?fcs) &*& scanf_parse_format(fcs, scanf_format, 0, varargs) == some(?targets) &*&
        switch (targets) {
            case nil: return ensures [fs]string(s, scs) &*& [f]string(format, fcs);
            case cons(t0, ts0): return scanf_targets(ts0, 0) &*&
                fst(t0) == 'i' ?
                    integer(fst(snd(t0)), _) &*& ensures [fs]string(s, scs) &*& [f]string(format, fcs) &*& integer(fst(snd(t0)), _) &*& scanf_targets(ts0, result - 1)
                : fst(t0) == 'c' ?
                    chars(fst(snd(t0)), snd(snd(t0)), _) &*& ensures [fs]string(s, scs) &*& [f]string(format, fcs) &*& chars(fst(snd(t0)), snd(snd(t0)), _) &*& scanf_targets(ts0, result - 1)
                :
                    chars(fst(snd(t0)), snd(snd(t0)) + 1, _) &*& ensures [fs]string(s, scs) &*& [f]string(format, fcs) &*& chars(fst(snd(t0)), snd(snd(t0)) + 1, ?cs) &*& result < 1 || mem('\0', cs) &*& scanf_targets(ts0, result - 1);
        };
    @*/
    //@ ensures emp;

#endif
