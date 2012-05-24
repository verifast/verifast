/*@

inductive value = K0 | K1(value) | S0 | S1(value) | S2(value, value);

inductive term = val(value) | app(term, term);

fixpoint term apply(value f, value v) {
    switch (f) {
        case K0: return val(K1(v));
        case K1(v0): return val(v0);
        case S0: return val(S1(v));
        case S1(v0): return val(S2(v0, v));
        case S2(v0, v1): return app(app(val(v0), val(v)), app(val(v1), val(v)));
    }
}

fixpoint term step(term t) {
    switch (t) {
        case val(v): return t;
        case app(t1, t2): return switch (t1) {
            case val(v1): return switch (t2) {
                case val(v2): return apply(v1, v2);
                default: return app(t1, step(t2));
            };
            default: return app(step(t1), t2);
        };
    }
}

predicate reduces_to(term t1, term t2) =
    t1 == t2 ? true : [_]reduces_to(step(t1), t2);

lemma void reduces_to_val(term t1, term t2)
    requires [_]reduces_to(t1, t2);
    ensures t1 == t2 ? true : t1 == app(_, _);
{
    open reduces_to(t1, t2);
    if (t1 == t2) {
    } else {
        switch (t1) { case val(v): case app(t11, t12): }
        reduces_to_val(step(t1), t2);
    }
}

// Lemmas that enable a recursive implementation

lemma void reduces_to_app_l(term t10, term t11, term t2)
    requires [_]reduces_to(t10, t11);
    ensures [_]reduces_to(app(t10, t2), app(t11, t2));
{
    open reduces_to(t10, t11);
    if (t10 == t11) {
    } else {
        reduces_to_app_l(step(t10), t11, t2);
        reduces_to_val(t10, t11);
    }
    close reduces_to(app(t10, t2), app(t11, t2));
}

lemma void reduces_to_app_r(value v, term t1, term t2)
    requires [_]reduces_to(t1, t2);
    ensures [_]reduces_to(app(val(v), t1), app(val(v), t2));
{
    open reduces_to(_, _);
    if (t1 == t2) {
    } else {
        reduces_to_app_r(v, step(t1), t2);
        reduces_to_val(t1, t2);
    }
    close reduces_to(app(val(v), t1), app(val(v), t2));
}

lemma void reduces_to_trans(term t1, term t2, term t3)
    requires [_]reduces_to(t1, t2) &*& [_]reduces_to(t2, t3);
    ensures [_]reduces_to(t1, t3);
{
    open reduces_to(t1, t2);
    if (t1 == t2) {
    } else {
        reduces_to_trans(step(t1), t2, t3);
        close reduces_to(t1, t3);
    }
}

@*/

final class Term {
    static final int tagAPP = 0;
    static final int tagK0 = 1;
    static final int tagK1 = 2;
    static final int tagS0 = 3;
    static final int tagS1 = 4;
    static final int tagS2 = 5;
    
    int tag;
    Term arg1;
    Term arg2;
    
    /*@
    
    predicate Term(term t) =
        [_]tag |-> ?tag &*& [_]arg1 |-> ?arg1 &*& [_]arg2 |-> ?arg2 &*&
        tag == tagAPP ?
            [_]arg1.Term(?t1) &*& [_]arg2.Term(?t2) &*& t == app(t1, t2)
        :
            [_]this.Value(?v) &*& t == val(v);
    
    predicate Value(value v) =
        [_]tag |-> ?tag &*& [_]arg1 |-> ?arg1 &*& [_]arg2 |-> ?arg2 &*&
        tag == tagK0 ? v == K0 :
        tag == tagK1 ? [_]arg1.Value(?v1) &*& v == K1(v1) :
        tag == tagS0 ? v == S0 :
        tag == tagS1 ? [_]arg1.Value(?v1) &*& v == S1(v1) :
        tag == tagS2 &*& [_]arg1.Value(?v1) &*& [_]arg2.Value(?v2) &*& v == S2(v1, v2);
    
    lemma void asTerm()
        requires [_]Value(?v);
        ensures [_]Term(val(v));
    {
    }
    
    @*/
    
    Term(int tag, Term arg1, Term arg2)
        //@ requires true;
        //@ ensures [_]this.tag |-> tag &*& [_]this.arg1 |-> arg1 &*& [_]this.arg2 |-> arg2;
    {
        this.tag = tag;
        this.arg1 = arg1;
        this.arg2 = arg2;
    }
    
    static Term mkApp(Term arg1, Term arg2)
        //@ requires [_]arg1.Term(?t1) &*& [_]arg2.Term(?t2);
        //@ ensures [_]result.Term(app(t1, t2));
    {
        return new Term(tagAPP, arg1, arg2);
    }
    
    static Term K0()
        //@ requires true;
        //@ ensures [_]result.Value(K0);
    {
        return new Term(tagK0, null, null);
    }
    
    static Term mkK1(Term arg)
        //@ requires [_]arg.Value(?v);
        //@ ensures [_]result.Value(K1(v));
    {
        return new Term(tagK1, arg, null);
    }
    
    static Term S0()
        //@ requires true;
        //@ ensures [_]result.Value(S0);
    {
        return new Term(tagS0, null, null);
    }
    
    static Term S1(Term arg)
        //@ requires [_]arg.Value(?v);
        //@ ensures result.Value(S1(v));
    {
        return new Term(tagS1, arg, null);
    }
    
    static Term S2(Term arg1, Term arg2)
        //@ requires [_]arg1.Value(?v1) &*& [_]arg2.Value(?v2);
        //@ ensures [_]result.Value(S2(v1, v2));
    {
        return new Term(tagS2, arg1, arg2);
    }
    
    Term apply_(Term v)
        //@ requires [_]Value(?vf) &*& [_]v.Value(?vv);
        //@ ensures [_]result.Value(?vr) &*& [_]reduces_to(apply(vf, vv), val(vr));
    {
        //@ close reduces_to(apply(vf, vv), apply(vf, vv));
        switch (tag) {
            case tagK0: return mkK1(v);
            case tagK1: return arg1;
            case tagS0: return S1(v);
            case tagS1: return S2(arg1, v);
            case tagS2:
                /*@ { arg1.asTerm(); arg2.asTerm(); v.asTerm(); } @*/
                return mkApp(mkApp(arg1, v), mkApp(arg2, v)).eval();
            default:
        }
    }
    
    Term eval()
        //@ requires [_]Term(?t);
        //@ ensures [_]result.Value(?v) &*& [_]reduces_to(t, val(v));
    {
        if (tag != tagAPP) {
            //@ close reduces_to(t, t);
            return this;
        }
        //@ assert [_]arg1 |-> ?a1 &*& [_]a1.Term(?t1) &*& [_]arg2 |-> ?a2 &*& [_]a2.Term(?t2);
        Term f = arg1.eval();
        //@ assert [_]f.Value(?vf);
        //@ reduces_to_app_l(t1, val(vf), t2);
        Term v = arg2.eval();
        //@ assert [_]v.Value(?vv);
        //@ reduces_to_app_r(vf, t2, val(vv));
        //@ reduces_to_trans(app(t1, t2), app(val(vf), t2), app(val(vf), val(vv)));
        Term r = f.apply_(v);
        //@ assert [_]r.Value(?vr);
        //@ close reduces_to(app(val(vf), val(vv)), val(vr));
        //@ reduces_to_trans(app(t1, t2), app(val(vf), val(vv)), val(vr));
        return r;
    }
}
