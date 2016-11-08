interface Func {
    //@ predicate valid(list<Class> level);
    /*@
    lemma void getClass_le_level();
        requires [_]valid(?level);
        ensures level_le({this.getClass()}, level) == true;
    @*/
    int apply(int x);
        //@ requires [_]valid(?level) &*& call_perm(level);
        //@ ensures true;
        //@ terminates;
}

class Util {
    static int deriv(Func f, int x)
        //@ requires [_]f.valid(?level) &*& call_perm(cons(Util.class, level));
        //@ ensures true;
        //@ terminates;
    {
        //@ call_perm_weaken(4);
        //@ f.getClass_le_level();
        //@ consume_call_perm_for(f.getClass());
        //@ consume_call_perm_for(f.getClass());
        return f.apply(x + 1) - f.apply(x);
    }
}

final class ZeroFunc implements Func {
    //@ predicate valid(list<Class> level) = level == {ZeroFunc.class};
    /*@
    lemma void getClass_le_level()
        requires [_]valid(?level);
        ensures level_le({this.getClass()}, level) == true;
    {
        open valid(_);
    }
    @*/
    ZeroFunc()
        //@ requires true;
        //@ ensures valid({ZeroFunc.class});
        //@ terminates;
    {
        //@ close valid({ZeroFunc.class});
    }
    public int apply(int x)
        //@ requires [_]valid(?level) &*& call_perm(level);
        //@ ensures true;
        //@ terminates;
    {
        return 0;
    }
}

final class PlusOneFunc implements Func {
    Func f;
    //@ predicate valid(list<Class> level) = f |-> ?f &*& [_]f.valid(?fLevel) &*& level == cons(PlusOneFunc.class, fLevel);
    /*@
    lemma void getClass_le_level()
        requires [_]valid(?level);
        ensures level_le({this.getClass()}, level) == true;
    {
        open valid(_);
    }
    @*/
    PlusOneFunc(Func f)
        //@ requires [_]f.valid(?fLevel);
        //@ ensures valid(cons(PlusOneFunc.class, fLevel));
        //@ terminates;
    {
        this.f = f;
    }
    public int apply(int x)
        //@ requires [_]valid(?level) &*& call_perm(level);
        //@ ensures true;
        //@ terminates;
    {
        //@ open valid(_);
        //@ call_perm_weaken(2);
        //@ f.getClass_le_level();
        //@ consume_call_perm_for(f.getClass());
        return f.apply(x) + 1;
    }
}

class Main {
    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        //@ assume(Class_lt(Util.class, Main.class));
        //@ assume(Class_lt(ZeroFunc.class, Main.class));
        //@ assume(Class_lt(PlusOneFunc.class, Main.class));

        Func f1 = new ZeroFunc();
        Func f2 = new PlusOneFunc(f1);
        Func f3 = new PlusOneFunc(f2);
        //@ produce_call_below_perm_();
        //@ call_below_perm__elim({Util.class, PlusOneFunc.class, PlusOneFunc.class, ZeroFunc.class});
        Util.deriv(f3, 0);
    }
}
