interface Func {
    //@ predicate valid(list<Class> level);
    /*@
    lemma void getClass_le_level();
        requires [_]valid(?level);
        ensures level_le({this.getClass()}, level) == true;
    @*/
    int apply(int x);
        //@ requires [_]valid(?level) &*& call_perm(currentThread, level);
        //@ ensures true;
        //@ terminates;
}

//@ predicate Func(Func f, list<Class> level;) = f.valid(?level0) &*& level_le(level0, level) == true;

class Util {
    static int apply(Func f, int x)
        //@ requires [_]Func(f, ?level) &*& [2]call_perm(currentThread, level);
        //@ ensures true;
        //@ terminates;
    {
        //@ open Func(_, _);
        //@ assert [_]f.valid(?level0);
        //@ call_perm_weaken(2, level0);
        //@ f.getClass_le_level();
        //@ consume_call_perm_for(f.getClass());
        return f.apply(x);
    }
    
    static int deriv(Func f, int x)
        //@ requires [_]Func(f, ?level) &*& call_perm(currentThread, cons(Util.class, level));
        //@ ensures true;
        //@ terminates;
    {
        //@ call_perm_weaken_and_dup(4);
        return apply(f, x + 1) - apply(f, x);
    }
    
    static int sum(Func f1, Func f2, int x)
        //@ requires [_]Func(f1, ?f1Level) &*& [_]Func(f2, ?f2Level) &*& call_perm(currentThread, cons(Util.class, level_max(f1Level, f2Level)));
        //@ ensures true;
        //@ terminates;
    {
        //@ call_perm_weaken_and_dup(4);
        //@ call_perm_weaken(2, f1Level);
        int y1 = apply(f1, x);
        //@ call_perm_weaken(2, f2Level);
        int y2 = apply(f2, x);
        return y1 + y2;
    }
    
    static int double_(Func f, int x)
        //@ requires [_]Func(f, ?fLevel) &*& call_perm(currentThread, cons(Util.class, fLevel));
        //@ ensures true;
        //@ terminates;
    {
        return sum(f, f, x);
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
        //@ requires [_]valid(?level) &*& call_perm(currentThread, level);
        //@ ensures true;
        //@ terminates;
    {
        return 0;
    }
    public static Func create()
        //@ requires true;
        //@ ensures Func(result, {ZeroFunc.class});
        //@ terminates;
    {
        Func f = new ZeroFunc();
        //@ close Func(f, {ZeroFunc.class});
        return f;
    }
}

final class PlusOneFunc implements Func {
    Func f;
    //@ list<Class> fLevel;
    //@ predicate valid(list<Class> level) = f |-> ?f &*& fLevel |-> ?fLevel &*& [_]Func(f, fLevel) &*& level == cons(PlusOneFunc.class, fLevel);
    /*@
    lemma void getClass_le_level()
        requires [_]valid(?level);
        ensures level_le({this.getClass()}, level) == true;
    {
        open valid(_);
    }
    @*/
    PlusOneFunc(Func f)
        //@ requires [_]Func(f, ?fLevel);
        //@ ensures valid(cons(PlusOneFunc.class, fLevel));
        //@ terminates;
    {
        this.f = f;
        //@ this.fLevel = fLevel;
    }
    public int apply(int x)
        //@ requires [_]valid(?level) &*& call_perm(currentThread, level);
        //@ ensures true;
        //@ terminates;
    {
        //@ open valid(_);
        //@ call_perm_weaken_and_dup(2);
        return Util.apply(f, x) + 1;
    }
    public static Func create(Func f)
        //@ requires [_]Func(f, ?fLevel) &*& call_perm(currentThread, cons(PlusOneFunc.class, fLevel));
        //@ ensures Func(result, cons(PlusOneFunc.class, fLevel));
        //@ terminates;
    {
        return new PlusOneFunc(f);
    }
}

final class SumFunc implements Func {
    Func f1;
    //@ list<Class> f1Level;
    Func f2;
    //@ list<Class> f2Level;
    
    /*@
    predicate valid(list<Class> level) =
        f1 |-> ?f1 &*& f1Level |-> ?f1Level &*& [_]Func(f1, f1Level) &*&
        f2 |-> ?f2 &*& f2Level |-> ?f2Level &*& [_]Func(f2, f2Level) &*&
        level == cons(SumFunc.class, level_max(f1Level, f2Level));
    @*/
    
    /*@
    lemma void getClass_le_level()
        requires [_]valid(?level);
        ensures level_le({this.getClass()}, level) == true;
    {
        open [_]valid(_);
    }
    @*/
    
    SumFunc(Func f1, Func f2)
        //@ requires [_]Func(f1, ?f1Level) &*& [_]Func(f2, ?f2Level);
        //@ ensures valid(cons(SumFunc.class, level_max(f1Level, f2Level)));
        //@ terminates;
    {
        this.f1 = f1;
        //@ this.f1Level = f1Level;
        this.f2 = f2;
        //@ this.f2Level = f2Level;
    }
    
    public int apply(int x)
        //@ requires [_]valid(?level) &*& call_perm(currentThread, level);
        //@ ensures true;
        //@ terminates;
    {
        //@ open [_]valid(_);
        //@ level_cons_mono_l(Util.class, SumFunc.class, level_max(f1Level, f2Level));
        //@ call_perm_weaken(1, cons(Util.class, level_max(f1Level, f2Level)));
        return Util.sum(f1, f2, x);
    }
    
    public static Func create(Func f1, Func f2)
        //@ requires [_]Func(f1, ?f1Level) &*& [_]Func(f2, ?f2Level) &*& call_perm(currentThread, cons(SumFunc.class, level_max(f1Level, f2Level)));
        //@ ensures Func(result, cons(SumFunc.class, level_max(f1Level, f2Level)));
        //@ terminates;
    {
        return new SumFunc(f1, f2);
    }
}

class Main {
    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        //@ produce_call_below_perm_();
        //@ list<Class> level = {Util.class, SumFunc.class, PlusOneFunc.class, ZeroFunc.class};
        //@ call_below_perm__elim(3, level);
        Func f1 = ZeroFunc.create();
        //@ leak Func(f1, _);
        //@ call_perm_weaken(1, {PlusOneFunc.class, ZeroFunc.class});
        Func f2 = PlusOneFunc.create(f1);
        //@ level_max_def({ZeroFunc.class}, {PlusOneFunc.class, ZeroFunc.class});
        //@ call_perm_weaken(1, cons(SumFunc.class, level_max({ZeroFunc.class}, {PlusOneFunc.class, ZeroFunc.class})));
        Func f3 = SumFunc.create(f1, f2);
        Util.deriv(f3, 0);
    }
}
