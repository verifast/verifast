/*@

predicate List(List l, list<int> elems, list<Class> level;) =
    l.valid(elems, ?level0) &*& elems == cons(_, _) &*&
    level_le({l.getClass()}, level0) == true &*& level_le(level0, level) == true;

lemma_auto void List_inv()
    requires List(?l, ?elems, ?level);
    ensures List(l, elems, level) &*& l != null &*& elems != nil;
{
    open List(_, _, _);
    close List(l, elems, level);
}

lemma void List_weaken(List l, list<Class> level)
    requires [?f]List(l, ?elems, ?level0) &*& level_le(level0, level) == true;
    ensures [f]List(l, elems, level);
{
    open List(l, elems, level0);
    assert [f]l.valid(elems, ?level00);
    level_le_trans(level00, level0, level);
    close [f]List(l, elems, level);
}

predicate List_opt(List l, list<int> elems, list<Class> level;) =
    l == null ?
        elems == nil
    :
        List(l, elems, level);

lemma void List_opt_weaken(List l, list<Class> level)
    requires [?f]List_opt(l, ?elems, ?level0) &*& level_le(level0, level) == true;
    ensures [f]List_opt(l, elems, level);
{
    open List_opt(l, elems, level0);
    if (l != null)
        List_weaken(l, level);
    close [f]List_opt(l, elems, level);
}

@*/

interface List {
    //@ predicate valid(list<int> elems, list<Class> level);
    int getHead();
        //@ requires [?f]valid(cons(?h, ?t), ?level) &*& call_perm(currentThread, level);
        //@ ensures [f]valid(cons(h, t), level) &*& result == h;
        //@ terminates;
    List getTail();
        //@ requires [?f]valid(cons(?h, ?t), ?level) &*& call_perm(currentThread, level);
        //@ ensures [f]List_opt(result, t, level);
        //@ terminates;
    List reverseAppend(List other);
        //@ requires valid(?elems, ?level) &*& List_opt(other, ?otherElems, ?otherLevel) &*& call_perm(currentThread, level);
        //@ ensures List(result, append(reverse(elems), otherElems), append(level, otherLevel));
        //@ terminates;
}

class ListUtil {
    static List reverseAppend(List l, List other)
        //@ requires List(l, ?elems, ?level) &*& List_opt(other, ?otherElems, ?otherLevel) &*& [2]call_perm(currentThread, level);
        //@ ensures List(result, append(reverse(elems), otherElems), append(level, otherLevel));
        //@ terminates;
    {
        //@ open List(l, _, _);
        //@ assert l.valid(_, ?level0);
        //@ call_perm_weaken(2, level0);
        //@ consume_call_perm_for(l.getClass());
        List result = l.reverseAppend(other);
        //@ level_append_mono_l(level0, level, otherLevel);
        //@ List_weaken(result, append(level, otherLevel));
        return result;
    }
    static List reverseAppend_opt(List l, List other)
        //@ requires List_opt(l, ?elems, ?level) &*& List_opt(other, ?otherElems, ?otherLevel) &*& call_perm(currentThread, cons(ListUtil.class, level));
        //@ ensures List_opt(result, append(reverse(elems), otherElems), append(level, otherLevel));
        //@ terminates;
    {
        //@ open List_opt(l, elems, level);
        if (l == null) {
            //@ level_le_append_r(level, otherLevel);
            //@ List_opt_weaken(other, append(level, otherLevel));
            return other;
        } else {
            //@ call_perm_weaken_and_dup(2);
            List result = reverseAppend(l, other);
            //@ close List_opt(result, append(reverse(elems), otherElems), append(level, otherLevel));
            return result;
        }
    }
    static List reverse_(List l)
        //@ requires List_opt(l, ?elems, ?level) &*& call_perm(currentThread, cons(ListUtil.class, level));
        //@ ensures List_opt(result, reverse(elems), level);
        //@ terminates;
    {
        //@ close List_opt(null, nil, nil);
        return reverseAppend_opt(l, null);
    }
}

final class Cons implements List {
    int value;
    List tail;
    //@ list<int> tailElems;
    //@ list<Class> tailLevel;
    /*@
    predicate valid(list<int> elems, list<Class> level) =
        value |-> ?value &*& tail |-> ?tail &*& tailElems |-> ?tailElems &*& tailLevel |-> ?tailLevel &*&
        List_opt(tail, tailElems, tailLevel) &*& elems == cons(value, tailElems) &*& level == cons(Cons.class, tailLevel);
    @*/
    Cons(int value, List tail)
        //@ requires List_opt(tail, ?tailElems, ?tailLevel);
        //@ ensures List(this, cons(value, tailElems), cons(Cons.class, tailLevel));
        //@ terminates;
    {
        this.value = value;
        this.tail = tail;
        //@ this.tailElems = tailElems;
        //@ this.tailLevel = tailLevel;
    }
    List reverseAppend(List other)
        //@ requires valid(?elems, ?level) &*& List_opt(other, ?otherElems, ?otherLevel) &*& call_perm(currentThread, level);
        //@ ensures List(result, append(reverse(elems), otherElems), append(level, otherLevel));
        //@ terminates;
    {
        //@ int v = value;
        List t = tail;
        //@ list<int> tElems = tailElems;
        //@ list<Class> tLevel = tailLevel;
        tail = other;
        //@ tailElems = otherElems;
        //@ tailLevel = otherLevel;
        //@ close List_opt(this, cons(v, otherElems), cons(Cons.class, otherLevel));
        //@ level_cons_mono_l(ListUtil.class, Cons.class, tLevel);
        //@ call_perm_weaken(1, cons(ListUtil.class, tLevel));
        List result = ListUtil.reverseAppend_opt(t, this);
        //@ length_append(reverse(tElems), cons(v, otherElems));
        //@ open List_opt(result, _, _);
        //@ append_assoc(reverse(tElems), {v}, otherElems);
        //@ level_le_append_flip(tLevel, {Cons.class});
        //@ append_assoc(tLevel, {Cons.class}, otherLevel);
        //@ level_append_mono_l(append(tLevel, {Cons.class}), level, otherLevel);
        //@ List_weaken(result, append(level, otherLevel));
        return result;
    }
    int getHead()
        //@ requires [?f]valid(cons(?h, ?t), ?level) &*& call_perm(currentThread, level);
        //@ ensures [f]valid(cons(h, t), level) &*& result == h;
        //@ terminates;
    {
        return value;
    }
    List getTail()
        //@ requires [?f]valid(cons(?h, ?t), ?level) &*& call_perm(currentThread, level);
        //@ ensures [f]List_opt(result, t, level);
        //@ terminates;
    {
        //@ open [_]valid(_, _);
        //@ assert [f]List_opt(_, t, ?tailLevel);
        //@ level_lt_cons(Cons.class, tailLevel);
        //@ List_opt_weaken(tail, level);
        return tail;
    }
}

class Main {
    static void main()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        //@ produce_call_below_perm_();
        //@ call_below_perm__elim(1, {ListUtil.class, Cons.class, Cons.class, Cons.class});
        //@ close List_opt(null, nil, nil);
        Cons c3 = new Cons(3, null);
        //@ close List_opt(c3, _, _);
        Cons c2 = new Cons(2, c3);
        //@ close List_opt(c2, _, _);
        Cons c1 = new Cons(1, c2);
        //@ close List_opt(c1, _, _);
        List rev = ListUtil.reverse_(c1);
        //@ assert List_opt(rev, {3, 2, 1}, _);
    }
}
