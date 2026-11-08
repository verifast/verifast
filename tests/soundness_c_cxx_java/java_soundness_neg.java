/* ========================================================================== */
/* Positive Verified Java Classes & Methods                                   */
/* ========================================================================== */

class Counter {
    int val;

    Counter(int v)
        //@ requires true;
        //@ ensures this.val |-> v;
    {
        this.val = v;
    }

    int getVal()
        //@ requires this.val |-> ?v;
        //@ ensures this.val |-> v &*& result == v;
    {
        return this.val;
    }

    void setVal(int v)
        //@ requires this.val |-> _;
        //@ ensures this.val |-> v;
    {
        this.val = v;
    }

    void inc()
        //@ requires this.val |-> ?v &*& v < 2147483647;
        //@ ensures this.val |-> v + 1;
    {
        this.val = this.val + 1;
    }

    int compute(int x)
        //@ requires this.val |-> ?v &*& 0 <= v && v < 1000 &*& 0 <= x && x < 1000;
        //@ ensures this.val |-> v &*& result > 0;
    {
        return this.val + x + 1;
    }
}

class SubCounter extends Counter {
    SubCounter(int v)
        //@ requires true;
        //@ ensures this.val |-> v;
    {
        super(v);
    }

    int compute(int x)
        //@ requires this.val |-> ?v &*& 0 <= v && v < 1000 &*& 0 <= x && x < 1000;
        //@ ensures this.val |-> v &*& result > 0; //~ should_fail
    {
        return -1;
    }
}

class java_soundness_neg {
    static int safe_abs(int x)
        //@ requires x != -2147483648;
        //@ ensures 0 <= result &*& (result == x || result == -x);
    {
        if (x < 0) {
            return -x;
        } else {
            return x;
        }
    }

    static int safe_array_get_set(int[] arr, int i, int n)
        //@ requires array_slice(arr, 0, n, ?elems) &*& 0 <= i && i < n;
        //@ ensures array_slice(arr, 0, n, _);
    {
        int v = arr[i];
        arr[i] = v;
        return v;
    }

    static void safe_object_ops()
        //@ requires true;
        //@ ensures true;
    {
        Counter c = new Counter(10);
        c.inc();
        int v = c.getVal();
        //@ assert v == 11;
    }

    /* ====================================================================== */
    /* Negative Soundness Tests (15 Should-Fail Cases)                        */
    /* ====================================================================== */

    /* 1. Null reference field read */
    static int neg_null_field_read(Counter c)
        //@ requires true;
        //@ ensures true;
    {
        return c.val; //~ should_fail
    }

    /* 2. Null reference field write */
    static void neg_null_field_write(Counter c)
        //@ requires true;
        //@ ensures true;
    {
        c.val = 42; //~ should_fail
    }

    /* 3. Null reference method call */
    static int neg_null_method_call(Counter c)
        //@ requires true;
        //@ ensures true;
    {
        return c.getVal(); //~ should_fail
    }

    /* 4. Array index out of bounds: index == length */
    static int neg_array_oob(int[] arr, int n)
        //@ requires array_slice(arr, 0, n, ?elems) &*& 0 <= n;
        //@ ensures array_slice(arr, 0, n, elems);
    {
        return arr[n]; //~ should_fail
    }

    /* 5. Array negative index read */
    static int neg_array_negative(int[] arr, int n)
        //@ requires array_slice(arr, 0, n, ?elems) &*& 0 < n;
        //@ ensures array_slice(arr, 0, n, elems);
    {
        return arr[-1]; //~ should_fail
    }

    /* 6. Array dereference on null array */
    static int neg_null_array_read()
        //@ requires true;
        //@ ensures true;
    {
        int[] arr = null;
        return arr[0]; //~ should_fail
    }

    /* 7. Division by constant zero */
    static int neg_div_const_zero(int x)
        //@ requires true;
        //@ ensures true;
    {
        return x / 0; //~ should_fail
    }

    /* 8. Modulo by constant zero */
    static int neg_mod_const_zero(int x)
        //@ requires true;
        //@ ensures true;
    {
        return x % 0; //~ should_fail
    }

    /* 9. Division by symbolic zero */
    static int neg_div_sym_zero(int x, int y)
        //@ requires y == 0;
        //@ ensures true;
    {
        return x / y; //~ should_fail
    }

    /* 10. Signed division overflow (Integer.MIN_VALUE / -1) */
    static int neg_div_overflow(int nom, int denom)
        //@ requires nom == -2147483648 && denom == -1;
        //@ ensures true;
    {
        return nom / denom; //~ should_fail
    }

    /* 11. Signed modulo overflow (Integer.MIN_VALUE % -1) */
    static int neg_mod_overflow(int nom, int denom)
        //@ requires nom == -2147483648 && denom == -1;
        //@ ensures true;
    {
        return nom % denom; //~ should_fail
    }

    /* 12. Invalid cast / instanceof assertion */
    static void neg_invalid_instanceof(Counter c)
        //@ requires c != null;
        //@ ensures true;
    {
        //@ assert c instanceof SubCounter; //~ should_fail
    }

    /* 13. Calling method with violated precondition */
    static void neg_method_precond_violation(Counter c)
        //@ requires c != null &*& c.val |-> 2147483647;
        //@ ensures true;
    {
        c.inc(); //~ should_fail
    }

    /* 14. Postcondition failure on mutated object field */
    static void neg_postcond_field_violation(Counter c)
        //@ requires c != null &*& c.val |-> 10;
        //@ ensures c.val |-> 10; //~ should_fail
    {
        c.setVal(20);
    }

    /* 15. Pure assertion failure */
    static void neg_assert_false()
        //@ requires true;
        //@ ensures true;
    {
        //@ assert false; //~ should_fail
    }
}
