#include <stdarg.h>
#include <stdio.h>

/*@

fixpoint int max(int x, int y) { return x < y ? y : x; }

fixpoint option<int> max_varargs(list<vararg> args) {
    switch (args) {
        case nil: return some(INT_MIN);
        case cons(arg, args0): return switch (arg) {
            case vararg_int(size, k): return
                size == sizeof(int) ?
                    switch (max_varargs(args0)) {
                        case none: return none;
                        case some(k0): return some(max(k, k0));
                    }
                :
                    none;
            default: return none;
        };
    }
}

lemma void max_varargs_ge_INT_MIN(list<vararg> args)
    requires max_varargs(args) == some(?k);
    ensures INT_MIN <= k;
{
    switch (args) {
        case nil:
        case cons(arg, args0):
            switch (arg) { default: }
            max_varargs_ge_INT_MIN(args0);
    }
}

@*/

int max_n(int n, ...)
//@ requires length(varargs) == n &*& max_varargs(varargs) == some(?k);
//@ ensures result == k;
{
    va_list ap;
    va_start(ap, n);
    int result = INT_MIN;
    //@ max_varargs_ge_INT_MIN(varargs);
    for (int i = 0; i < n; i++)
    //@ invariant n |-> ?n_ &*& i <= n_ &*& ap |-> ?ap_ &*& va_list(ap_, &n, 1/2, ?args) &*& length(args) == n_ - i &*& max_varargs(args) == some(?k1) &*& max(result, k1) == k;
    {
        int v = va_arg(ap, int);
        if (result < v)
            result = v;
    }
    //@ assert n |-> ?n_ &*& ap |-> ?ap_ &*& va_list(ap_, &n, 1/2, ?args) &*& length(args) == 0 &*& max_varargs(args) == some(?k1) &*& max(result, k1) == k;
    //@ switch (args) { case nil: case cons(h, t): }
    va_end(ap);

    return result;
}

void error(char *function_name, char *format, ...)
    /*@
    requires
        [?ff]string(function_name, ?fncs) &*& [?f]string(format, ?fcs) &*& printf_parse_format(fcs, varargs) == some(?ps) &*&
        switch (ps) {
            case nil: return ensures [ff]string(function_name, fncs) &*& [f]string(format, fcs);
            case cons(p0, ps0): return [?f0]string(p0, ?cs0) &*&
                switch (ps0) {
                    case nil: return ensures [ff]string(function_name, fncs) &*& [f]string(format, fcs) &*& [f0]string(p0, cs0);
                    case cons(p1, ps1): return [?f1]string(p1, ?cs1) &*&
                        switch (ps1) {
                            case nil: return ensures [ff]string(function_name, fncs) &*& [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1);
                            case cons(p2, ps2): return [?f2]string(p2, ?cs2) &*&
                                switch (ps2) {
                                    case nil: return ensures [ff]string(function_name, fncs) &*& [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1) &*& [f2]string(p2, cs2);
                                    case cons(p3, ps3): return [?f3]string(p3, ?cs3) &*&
                                        switch (ps3) {
                                            case nil: return ensures [ff]string(function_name, fncs) &*& [f]string(format, fcs) &*& [f0]string(p0, cs0) &*& [f1]string(p1, cs1) &*& [f2]string(p2, cs2) &*& [f3]string(p3, cs3);
                                            case cons(p4, ps4): return false; // TODO: Support more string arguments...
                                        };
                                };
                        };
                };
        };
    @*/
    //@ ensures emp;
{
    va_list args;
    va_start(args, format);
    fprintf(stderr, "ERROR in %s: ", function_name);
    vfprintf(stderr, format, args);
    va_end(args);
}
