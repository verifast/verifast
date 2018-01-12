#ifndef BEEP_H
#define BEEP_H

//@ #include "abstract_io.gh"

/*@

predicate beep_(predicate() P, predicate() Q);

lemma void beep__weaken(predicate() P1, predicate() P2, predicate() Q1, predicate() Q2);
    requires beep_(P2, Q1) &*& conseq(P1, P2, Q1, Q2);
    ensures beep_(P1, Q2);

@*/

void beep();
    //@ requires token(?P) &*& beep_(P, ?Q);
    //@ ensures token(Q);

#endif
