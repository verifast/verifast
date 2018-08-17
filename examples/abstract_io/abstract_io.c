//@ #include "abstract_io.gh"

/*@

lemma void modus_ponens()
    requires is_implies(?imp, ?P1, ?P2, ?Q1, ?Q2) &*& P1() &*& P2();
    ensures Q1() &*& Q2();
{
    imp();
    leak is_implies(imp, P1, P2, Q1, Q2);
}

lemma void conseq_refl(predicate() P, predicate() Q)
    requires true;
    ensures conseq(P, P, Q, Q);
{
    implies_refl(P, True);
    implies_refl(Q, True);
    close conseq(P, P, Q, Q);
}

lemma void conseq_elim()
    requires token(?P1) &*& conseq(P1, ?P2, ?Q1, ?Q2);
    ensures P2() &*& is_implies(_, Q1, ?Frame, Q2, True) &*& Frame();
{
    open token(P1);
    open conseq(P1, P2, Q1, Q2);
    assert is_implies(?imp1, P1, True, P2, ?Frame);
    imp1();
    leak is_implies(imp1, P1, True, P2, Frame);
}

lemma void do_split()
    requires split_(?P, ?Q1, ?Q2) &*& token(P);
    ensures token(Q1) &*& token(Q2);
{
    open split_(_, _, _);
    open token(P);
    assert is_implies(?lem, _, _, _, _);
    lem();
    close token(Q1);
    close token(Q2);
    leak is_implies(_, _, _, _, _);
}

@*/
