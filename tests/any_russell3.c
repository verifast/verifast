//@ #include <quantifiers.gh>

/*@

inductive set<t> = set(t f);

fixpoint bool Raux(any s, fixpoint(any, bool) f) {
    return
        s != set(f) //~ should_fail
    ||
        !f(s);
}

fixpoint bool R(fixpoint(fixpoint(fixpoint(any, bool), bool), bool) forall_f, any s) { return forall_f((Raux)(s)); }

lemma void Russell_paradox()
    requires true;
    ensures false;
{
    get_forall_t<fixpoint(any, bool)>();
    assert [_]is_forall_t(?forall_f);
    fixpoint(any, bool) fR = (R)(forall_f);
    if (fR(set(fR))) {
        forall_t_elim(forall_f, (Raux)(set(fR)), fR);
    } else {
        not_forall_t<fixpoint(any, bool)>(forall_f, (Raux)(set(fR)));
    }
}

@*/
