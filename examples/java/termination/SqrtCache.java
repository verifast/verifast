final class DoubleMap {
    //@ predicate valid();
    
    DoubleMap()
        //@ requires obs(?O) &*& wait_level_below_obs(pair({DoubleMap.class}, 0r), O) == true;
        //@ ensures obs(O) &*& valid();
        //@ terminates;
    { throw new RuntimeException(); }

    boolean containsKey(double key)
        //@ requires valid() &*& obs(?O) &*& wait_level_below_obs(pair({DoubleMap.class}, 0r), O) == true;
        //@ ensures valid() &*& obs(O);
        //@ terminates;
    { throw new RuntimeException(); }

    double get(double key)
        //@ requires valid() &*& obs(?O) &*& wait_level_below_obs(pair({DoubleMap.class}, 0r), O) == true;
        //@ ensures valid() &*& obs(O);
        //@ terminates;
    { throw new RuntimeException(); }

    void put(double key, double value)
        //@ requires valid() &*& obs(?O) &*& wait_level_below_obs(pair({DoubleMap.class}, 0r), O) == true;
        //@ ensures valid() &*& obs(O);
        //@ terminates;
    { throw new RuntimeException(); }
}

//@ predicate_ctor Math_inv(Math math)() = math.sqrtCache |-> ?sqrtCache &*& sqrtCache.valid();

final class Math {
    DoubleMap sqrtCache;
    Lock sqrtCacheLock;

    /*@
    predicate valid() =
        sqrtCacheLock |-> ?lock &*& lock.lock(Math_inv(this))
        &*& wait_level_of(lock) == pair({Math.class}, 0r);
    @*/
    
    Math()
        //@ requires obs(?O) &*& wait_level_below_obs(pair({Math.class}, 0r), O) == true;
        //@ ensures obs(O) &*& [_]valid();
        //@ terminates;
    {
        //@ wait_level_lt_below_obs(pair({DoubleMap.class}, 0r), pair({Math.class}, 0r), O);
        sqrtCache = new DoubleMap();
        //@ close Math_inv(this)();
        //@ close exists(Math_inv(this));
        //@ close exists(pair({Math.class}, 0r));
        sqrtCacheLock = new Lock();
    }
    
    private static double sqrt_(double x)
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        throw new RuntimeException();
    }

    double sqrt(double x)
        //@ requires [_]valid() &*& obs(?O) &*& wait_level_below_obs(pair({Math.class}, 0r), O) == true;
        //@ ensures obs(O);
        //@ terminates;
    {
        return sqrt_(x);
    }

    double sqrtCached(double x)
        //@ requires [_]valid() &*& obs(?O) &*& wait_level_below_obs(pair({Math.class}, 0r), O) == true;
        //@ ensures obs(O);
        //@ terminates;
    {
        //@ wait_level_lt_below_obs(pair({DoubleMap.class}, 0r), pair({Math.class}, 0r), O);
        sqrtCacheLock.acquire();
        //@ open Math_inv(this)();
        if (!sqrtCache.containsKey(x))
            sqrtCache.put(x, sqrt_(x));
        double result = sqrtCache.get(x);
        //@ close Math_inv(this)();
        sqrtCacheLock.release();
        return result;
    }
}

class Main {
    static void main(double x)
        //@ requires obs(?O) &*& wait_level_below_obs(pair({Main.class}, 0r), O) == true;
        //@ ensures obs(O);
        //@ terminates;
    {
        //@ wait_level_lt_below_obs(pair({Math.class}, 0r), pair({Main.class}, 0r), O);
        Math math = new Math();
        math.sqrtCached(x);
    }
}
