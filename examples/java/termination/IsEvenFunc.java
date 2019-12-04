interface IsEvenFunc {
    //@ predicate valid(list<Class> level);
    /*@
    lemma void getClass_le_level();
        requires [_]valid(?level);
        ensures level_le({this.getClass()}, level) == true;
    @*/
    boolean isEven(IsOddFunc f, int n);
        //@ requires [_]valid(?level) &*& [_]f.valid(?fLevel) &*& 0 <= n &*& call_perm_rec(currentThread, level_max(level, fLevel), int_lt, n);
        //@ ensures true;
        //@ terminates;
}

interface IsOddFunc {
    //@ predicate valid(list<Class> level);
    /*@
    lemma void getClass_le_level();
        requires [_]valid(?level);
        ensures level_le({this.getClass()}, level) == true;
    @*/
    boolean isOdd(IsEvenFunc f, int n);
        //@ requires [_]valid(?level) &*& [_]f.valid(?fLevel) &*& 0 <= n &*& call_perm_rec(currentThread, level_max(fLevel, level), int_lt, n);
        //@ ensures true;
        //@ terminates;
}

class Util {
    static boolean isEven(IsEvenFunc e, IsOddFunc o, int n)
        //@ requires [_]e.valid(?eLevel) &*& [_]o.valid(?oLevel) &*& 0 <= n &*& call_perm(currentThread, cons(Util.class, level_max(eLevel, oLevel)));
        //@ ensures true;
        //@ terminates;
    {
        //@ is_wf_int_lt();
        //@ create_call_perm_rec(2, level_max(eLevel, oLevel), int_lt, n);
        //@ call_perm_rec_elim(1);
        //@ e.getClass_le_level();
        //@ level_le_append_l(eLevel, oLevel);
        //@ level_le_trans({e.getClass()}, eLevel, level_max(eLevel, oLevel));
        //@ consume_call_perm_for(e.getClass());
        return e.isEven(o, n);
    }
}

final class MyIsEvenFunc implements IsEvenFunc {
    //@ predicate valid(list<Class> level) = level == {MyIsEvenFunc.class};
    /*@
    lemma void getClass_le_level()
        requires [_]valid(?level);
        ensures level_le({this.getClass()}, level) == true;
    {
        open [_]valid(_);
    }
    @*/
    MyIsEvenFunc()
        //@ requires true;
        //@ ensures valid({MyIsEvenFunc.class});
        //@ terminates;
    {
        //@ close valid({MyIsEvenFunc.class});
    }
    boolean isEven(IsOddFunc f, int n)
        //@ requires [_]valid(?level) &*& [_]f.valid(?fLevel) &*& 0 <= n &*& call_perm_rec(currentThread, level_max(level, fLevel), int_lt, n);
        //@ ensures true;
        //@ terminates;
    {
        /*@
        if (0 < n) {
            call_perm_rec_weaken(2, n - 1);
            call_perm_rec_elim(1);
            f.getClass_le_level();
            level_le_append_r(level, fLevel);
            level_le_trans({f.getClass()}, fLevel, level_max(level, fLevel));
            consume_call_perm_for(f.getClass());
        }
        @*/
        return n == 0 || f.isOdd(this, n - 1);
    }
}

final class MyIsOddFunc implements IsOddFunc {
    //@ predicate valid(list<Class> level) = level == {MyIsOddFunc.class};
    /*@
    lemma void getClass_le_level()
        requires [_]valid(?level);
        ensures level_le({this.getClass()}, level) == true;
    {
        open [_]valid(_);
    }
    @*/
    MyIsOddFunc()
        //@ requires true;
        //@ ensures valid({MyIsOddFunc.class});
        //@ terminates;
    {
        //@ close valid({MyIsOddFunc.class});
    }
    boolean isOdd(IsEvenFunc f, int n)
        //@ requires [_]valid(?level) &*& [_]f.valid(?fLevel) &*& 0 <= n &*& call_perm_rec(currentThread, level_max(fLevel, level), int_lt, n);
        //@ ensures true;
        //@ terminates;
    {
        /*@
        if (0 < n) {
            call_perm_rec_weaken(2, n - 1);
            call_perm_rec_elim(1);
            f.getClass_le_level();
            level_le_append_l(fLevel, level);
            level_le_trans({f.getClass()}, fLevel, level_max(fLevel, level));
            consume_call_perm_for(f.getClass());
        }
        @*/
        return n != 0 && f.isEven(this, n - 1);
    }
}

class Main {
    static void main()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        IsEvenFunc e = new MyIsEvenFunc();
        IsOddFunc o = new MyIsOddFunc();
        //@ produce_call_below_perm_();
        //@ level_max_def({MyIsEvenFunc.class}, {MyIsOddFunc.class});
        //@ call_below_perm__elim(1, {Util.class, MyIsOddFunc.class});
        Util.isEven(e, o, 42);
    }
}
