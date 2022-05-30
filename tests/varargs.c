#include <stdarg.h>

/*@

fixpoint int max(int x, int y) { return x < y ? y : x; }

fixpoint option<int> max_varargs(list<vararg> args) {
    switch (args) {
        case nil: return some(INT_MIN);
        case cons(arg, args0): return switch (arg) {
            case vararg_int(k): return switch (max_varargs(args0)) {
                case none: return none;
                case some(k0): return some(max(k, k0));
            };
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
            switch (arg) { case vararg_int(i): case vararg_uint(u): case vararg_pointer(p): }
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


