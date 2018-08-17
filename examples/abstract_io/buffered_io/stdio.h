#ifndef STDIO_H
#define STDIO_H

//@ #include "abstract_io.gh"

/*@

predicate putchar_(predicate() P, char c, predicate() Q);

lemma void putchar__weaken();
    requires putchar_(?P2, ?c, ?Q1) &*& conseq(?P1, P2, Q1, ?Q2);
    ensures putchar_(P1, c, Q2);

@*/

void putchar(char c);
    //@ requires token(?P) &*& putchar_(P, c, ?Q);
    //@ ensures token(Q);

/*@

predicate flush_(predicate() P, predicate() Q);

lemma void flush__weaken();
    requires flush_(?P2, ?Q1) &*& conseq(?P1, P2, Q1, ?Q2);
    ensures flush_(P1, Q2);

@*/

void flush();
    //@ requires token(?P) &*& flush_(P, ?Q);
    //@ ensures token(Q);

#endif
