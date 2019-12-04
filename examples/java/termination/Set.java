interface Set {
    //@ predicate valid(list<Class> level);
    /*@
    lemma void getClass_le_level();
        requires [_]valid(?level);
        ensures level_le({this.getClass()}, level) == true;
    @*/
    boolean contains(int x);
        //@ requires [_]valid(?level) &*& call_perm(currentThread, level);
        //@ ensures true;
        //@ terminates;
    boolean intersects(Set other);
        //@ requires [_]valid(?level) &*& [_]Set(other, ?otherLevel) &*& call_perm(currentThread, append(level, otherLevel));
        //@ ensures true;
        //@ terminates;
}

/*@
predicate Set(Set set, list<Class> level;) = set.valid(?level0) &*& level_le(level0, level) == true;
@*/

class SetHelper {
    static boolean contains(Set set, int x)
        //@ requires [_]Set(set, ?level) &*& [2]call_perm(currentThread, level);
        //@ ensures true;
        //@ terminates;
    {
        //@ open [_]Set(set, level);
        //@ assert [_]set.valid(?level0);
        //@ call_perm_weaken(2, level0);
        //@ set.getClass_le_level();
        //@ consume_call_perm_for(set.getClass());
        return set.contains(x);
    }

    static boolean intersects(Set set, Set other)
        //@ requires [_]Set(set, ?level) &*& [_]Set(other, ?otherLevel) &*& [2]call_perm(currentThread, append(level, otherLevel));
        //@ ensures true;
        //@ terminates;
    {
        //@ open [_]Set(set, level);
        //@ assert [_]set.valid(?level0);
        //@ level_append_mono_l(level0, level, otherLevel);
        //@ call_perm_weaken(2, append(level0, otherLevel));
        //@ set.getClass_le_level();
        //@ level_le_append_l(level0, otherLevel);
        //@ level_le_trans({set.getClass()}, level0, append(level0, otherLevel));
        //@ consume_call_perm_for(set.getClass());
        return set.intersects(other);
    }
}

final class Empty implements Set {
    //@ predicate valid(list<Class> level) = level == {Empty.class};
    /*@
    lemma void getClass_le_level()
        requires [_]valid(?level);
        ensures level_le({this.getClass()}, level) == true;
    {
        open [_]valid(_);
    }
    @*/
    Empty()
        //@ requires true;
        //@ ensures valid({Empty.class});
        //@ terminates;
    {
        //@ close valid({Empty.class});
    }
    public boolean contains(int x)
        //@ requires [_]valid(?level) &*& call_perm(currentThread, level);
        //@ ensures true;
        //@ terminates;
    {
        return false;
    }
    public boolean intersects(Set other)
        //@ requires [_]valid(?level) &*& [_]Set(other, ?otherLevel) &*& call_perm(currentThread, append(level, otherLevel));
        //@ ensures true;
        //@ terminates;
    {
        return false;
    }
    public static Set create()
        //@ requires true;
        //@ ensures [_]Set(result, {Empty.class});
        //@ terminates;
    {
        return new Empty();
    }
}

final class Insert implements Set {
    int elem;
    Set set;
    //@ list<Class> setLevel;
    //@ predicate valid(list<Class> level) = elem |-> _ &*& set |-> ?set &*& setLevel |-> ?setLevel &*& [_]Set(set, setLevel) &*& level == cons(Insert.class, setLevel);
    /*@
    lemma void getClass_le_level()
        requires [_]valid(?level);
        ensures level_le({this.getClass()}, level) == true;
    {
        open [_]valid(_);
    }
    @*/
    public Insert(int elem, Set set)
        //@ requires [_]Set(set, ?setLevel);
        //@ ensures valid(cons(Insert.class, setLevel));
        //@ terminates;
    {
        this.elem = elem;
        this.set = set;
        //@ this.setLevel = setLevel;
    }
    public boolean contains(int x)
        //@ requires [_]valid(?level) &*& call_perm(currentThread, level);
        //@ ensures true;
        //@ terminates;
    {
        //@ open [_]valid(_);
        //@ call_perm_weaken_and_dup(2);
        return x == elem || SetHelper.contains(set, x);
    }
    public boolean intersects(Set other)
        //@ requires [_]valid(?level) &*& [_]Set(other, ?otherLevel) &*& call_perm(currentThread, append(level, otherLevel));
        //@ ensures true;
        //@ terminates;
    {
        //@ open [_]valid(_);
        Set set = this.set;
        //@ assert [_]Set(set, ?setLevel);
        //@ call_perm_weaken_and_dup(4);
        //@ level_le_append_r(setLevel, otherLevel);
        //@ call_perm_weaken(2, otherLevel);
        return SetHelper.contains(other, elem) || SetHelper.intersects(set, other);
    }
    public static Set create(int elem, Set set)
        //@ requires [_]Set(set, ?setLevel) &*& call_perm(currentThread, cons(Insert.class, setLevel));
        //@ ensures [_]Set(result, cons(Insert.class, setLevel));
        //@ terminates;
    {
        return new Insert(elem, set);
    }
}

class Util {
    public static boolean intersects(Set s1, Set s2)
        //@ requires [_]Set(s1, ?s1Level) &*& [_]Set(s2, ?s2Level) &*& call_perm(currentThread, cons(Util.class, append(s1Level, s2Level)));
        //@ ensures true;
        //@ terminates;
    {
        //@ call_perm_weaken_and_dup(2);
        return SetHelper.intersects(s1, s2);
    }
}

class Main {
    public static void main()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        //@ produce_call_below_perm_();
        //@ call_below_perm__elim(2, {Util.class, Insert.class, Empty.class, Insert.class, Empty.class});
        Set s1 = Empty.create();
        //@ call_perm_weaken(1, {Insert.class, Empty.class});
        Set s2 = Insert.create(42, s1);
        Util.intersects(s2, s2);
    }
}