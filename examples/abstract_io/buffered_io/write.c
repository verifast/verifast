#include "write.h"

/*@

lemma void write_chars__add()
    requires write_chars_(?P, ?cs1, ?Q) &*& write_char_(Q, ?c, ?R);
    ensures write_chars_(P, append(cs1, {c}), R);
{
    open write_chars_(P, cs1, Q);
    switch (cs1) {
        case nil:
            implies_refl(R, True);
            close conseq(P, Q, R, R);
            write_char__weaken(P, Q, c, R, R);
            implies_refl(R, True);
            close write_chars_(R, nil, R);
            close write_chars_(P, {c}, R);
        case cons(c0, cs0):
            write_chars__add();
            close write_chars_(P, append(cs1, {c}), R);
    }
}

@*/
