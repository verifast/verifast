//@ #include <quantifiers.gh>

/*@

inductive set = set(fixpoint(any, bool) f); //~ should_fail

fixpoint bool Raux(any s, fixpoint(any, bool) f) { return s != set(f) || !f(s); }

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
