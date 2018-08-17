#ifndef WRITE_H
#define WRITE_H

//@ #include "abstract_io.gh"

/*@

predicate write_char_(predicate() P, char c, predicate() Q);

lemma void write_char__weaken(predicate() P1, predicate() P2, char c, predicate() Q1, predicate() Q2);
    requires write_char_(P2, c, Q1) &*& conseq(P1, P2, Q1, Q2);
    ensures write_char_(P1, c, Q2);

predicate write_chars_(predicate() P, list<char> cs, predicate() Q) =
    switch (cs) {
        case nil: return is_implies(_, P, True, Q, True);
        case cons(c, cs0): return write_char_(P, c, ?R) &*& write_chars_(R, cs0, Q);
    };

lemma void write_chars__add();
    requires write_chars_(?P, ?cs1, ?Q) &*& write_char_(Q, ?c, ?R);
    ensures write_chars_(P, append(cs1, {c}), R);

@*/

void write_stdout(char *buffer, int size);
    //@ requires [?f]buffer[..size] |-> ?cs &*& token(?P) &*& write_chars_(P, cs, ?Q);
    //@ ensures [f]buffer[..size] |-> cs &*& token(Q);

#endif
