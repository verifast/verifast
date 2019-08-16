//@ #include <quantifiers.gh>

/*@

inductive any_ = any_(any);

inductive set = set(fixpoint(any_, bool) f);

fixpoint bool Raux(any_ s, fixpoint(any_, bool) f) {
    return
        s !=
            any_(set(f)) //~ should_fail
    ||
        !f(s);
}

fixpoint bool R(fixpoint(fixpoint(fixpoint(any_, bool), bool), bool) forall_f, any_ s) { return forall_f((Raux)(s)); }

lemma void Russell_paradox()
    requires true;
    ensures false;
{
    get_forall_t<fixpoint(any_, bool)>();
    assert [_]is_forall_t(?forall_f);
    fixpoint(any_, bool) fR = (R)(forall_f);
    if (fR(any_(set(fR)))) {
        forall_t_elim(forall_f, (Raux)(any_(set(fR))), fR);
    } else {
        not_forall_t<fixpoint(any_, bool)>(forall_f, (Raux)(any_(set(fR))));
    }
}

@*/
