interface Counter {
    /*@

    predicate Counter(int value);

    lemma void inv();
        requires [?f]Counter(?value);
        ensures [f]Counter(value) &*& 0 <= value;

    @*/

    public int get();
        //@ requires [?f]Counter(?value);
        //@ ensures [f]Counter(value) &*& result == value;

    public void set(int value);
        //@ requires Counter(_) &*& 0 <= value;
        //@ ensures Counter(value);
}

class MyCounter implements Counter {
    int count;

    /*@

    predicate Counter(int value) = count |-> value &*& 0 <= value;

    lemma void inv()
        requires [?f]Counter(?value);
        ensures [f]Counter(value) &*& 0 <= value;
    {
        open Counter(value);
        close [f]Counter(value);
    }

    @*/

    MyCounter()
        //@ requires true;
        //@ ensures Counter(0);
    {
        //@ close Counter(0);
    }

    public int get()
        //@ requires [?f]Counter(?value);
        //@ ensures [f]Counter(value) &*& result == value;
    {
        //@ open Counter(value);
        return count;
        //@ close [f]Counter(value);
    }

    public void set(int value)
        //@ requires Counter(_) &*& 0 <= value;
        //@ ensures Counter(value);
    {
        //@ open Counter(_);
        count = value;
        //@ close Counter(value);
    }
}

class Program {
    public static void test(Counter c)
        //@ requires [?f]c.Counter(?value_);
        //@ ensures [f]c.Counter(value_);
    {
        int value = c.get();
        //@ c.inv();
        assert 0 <= value;
    }

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Counter c = new MyCounter();
        c.set(42);
        test(c);
    }
}