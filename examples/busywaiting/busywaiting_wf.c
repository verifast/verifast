//@ #include <quantifiers.gh>
#include "busywaiting.h"

/*@

fixpoint bool chain0_descends_at(nat max_length, fixpoint(int, list<int>) chain, int i) {
    return i < 0 || lex0_lt(int_of_nat(max_length), chain(i + 1), chain(i));
}

fixpoint bool starts_with_from(fixpoint(int, list<int>) chain, int h, int i, int j) {
    return j < i || length(chain(j)) > 0 && head(chain(j)) == h;
}

fixpoint list<int> tail_chain(fixpoint(int, list<int>) chain, int i, int j) {
    return tail(chain(i + j));
}

lemma void lex0_lt_wf(nat max_length, fixpoint(int, list<int>) chain)
    requires forall_int((chain0_descends_at)(max_length, chain)) == true;
    ensures false;
{
    switch (max_length) {
        case zero:
            forall_int_elim((chain0_descends_at)(max_length, chain), 0);
            lex0_lt_nonpos_max_length(0, chain(1), chain(0));
            assert false;
        case succ(max_length0):
            switch (chain(0)) {
                case nil:
                    switch (chain(1)) { case nil: case cons(h1, t1): }
                    forall_int_elim((chain0_descends_at)(max_length, chain), 0);
                    assert false;
                case cons(c0h, c0t):
                    int h = c0h;
                    int i = 0;
                    while (0 <= h)
                        invariant 0 <= i &*& chain(i) == cons(h, _);
                        decreases h;
                    {
                        if (forall_int((starts_with_from)(chain, h, i))) {
                            if (!forall_int((chain0_descends_at)(max_length0, (tail_chain)(chain, i)))) {
                                int j = not_forall_int((chain0_descends_at)(max_length0, (tail_chain)(chain, i)));
                                forall_int_elim((chain0_descends_at)(max_length, chain), i + j);
                                forall_int_elim((starts_with_from)(chain, h, i), i + j);
                                forall_int_elim((starts_with_from)(chain, h, i), i + j + 1);
                                assert chain(i + j) == cons(?hij, _);
                                assert chain(i + j + 1) == cons(?hij1, _);
                                assert false;
                            }
                            lex0_lt_wf(max_length0, (tail_chain)(chain, i));
                            assert false;
                        }
                        int i1 = not_forall_int((starts_with_from)(chain, h, i));
                        int newh = 0;
                        while (i < i1)
                            invariant 0 <= i &*& i <= i1 &*& chain(i) == cons(h, _);
                            decreases i1 - i;
                        {
                            if (chain(i + 1) == nil) {
                                forall_int_elim((chain0_descends_at)(max_length, chain), i + 1);
                                switch (chain(i + 2)) { case nil: case cons(hi2, ti2): }
                                assert false;
                            }
                            assert chain(i + 1) == cons(?h1, _);
                            forall_int_elim((chain0_descends_at)(max_length, chain), i);
                            if (h1 == h) {
                                i++;
                            } else {
                                newh = h1;
                                i++;
                                break;
                            }
                        }
                        h = newh;
                    }
                    {
                        if (forall_int((starts_with_from)(chain, h, i))) {
                            if (!forall_int((chain0_descends_at)(max_length0, (tail_chain)(chain, i)))) {
                                int j = not_forall_int((chain0_descends_at)(max_length0, (tail_chain)(chain, i)));
                                forall_int_elim((chain0_descends_at)(max_length, chain), i + j);
                                forall_int_elim((starts_with_from)(chain, h, i), i + j);
                                forall_int_elim((starts_with_from)(chain, h, i), i + j + 1);
                                assert chain(i + j) == cons(?hij, _);
                                assert chain(i + j + 1) == cons(?hij1, _);
                                assert false;
                            }
                            lex0_lt_wf(max_length0, (tail_chain)(chain, i));
                            assert false;
                        }
                        int i1 = not_forall_int((starts_with_from)(chain, h, i));
                        while (i < i1)
                            invariant 0 <= i &*& i <= i1 &*& chain(i) == cons(h, _);
                            decreases i1 - i;
                        {
                            if (chain(i + 1) == nil) {
                                forall_int_elim((chain0_descends_at)(max_length, chain), i + 1);
                                switch (chain(i + 2)) { case nil: case cons(hi2, ti2): }
                                assert false;
                            }
                            assert chain(i + 1) == cons(?h1, _);
                            forall_int_elim((chain0_descends_at)(max_length, chain), i);
                            if (h1 == h) {
                                i++;
                            } else {
                                assert false;
                            }
                        }
                    }
            }
    }
}

fixpoint bool chain_descends_at(fixpoint(int, list<int>) chain, int i) {
    return i < 0 || lex_lt(chain(i + 1), chain(i));
}

lemma void lex_lt_wf(fixpoint(int, list<int>) chain)
    requires forall_int((chain_descends_at)(chain)) == true;
    ensures false;
{
    switch (chain(0)) {
        case nil:
            forall_int_elim((chain_descends_at)(chain), 0);
            switch (chain(1)) { case nil: case cons(h1, t1): }
            assert false;
        case cons(max_length, c0t):
            if (max_length <= 0) {
                forall_int_elim((chain_descends_at)(chain), 0);
                assert chain(1) == cons(max_length, ?c1t);
                lex0_lt_nonpos_max_length(max_length, c1t, c0t);
                assert false;
            }
            if (!forall_int((starts_with_from)(chain, max_length, 0))) {
                int i = not_forall_int((starts_with_from)(chain, max_length, 0));
                for (int j = 0; j < i; j++)
                    invariant 0 <= j &*& j <= i &*& chain(j) == cons(max_length, _);
                    decreases i - j;
                {
                    forall_int_elim((chain_descends_at)(chain), j);
                    switch (chain(j + 1)) {
                        case nil:
                        case cons(hj1, tj1):
                    }
                }
                assert false;
            }
            if (!forall_int((chain0_descends_at)(nat_of_int(max_length), (tail_chain)(chain, 0)))) {
                int i = not_forall_int((chain0_descends_at)(nat_of_int(max_length), (tail_chain)(chain, 0)));
                forall_int_elim((starts_with_from)(chain, max_length, 0), i);
                forall_int_elim((starts_with_from)(chain, max_length, 0), i + 1);
                assert chain(i) == cons(max_length, _);
                assert chain(i + 1) == cons(max_length, _);
                forall_int_elim((chain_descends_at)(chain), i);
                assert false;
            }
            lex0_lt_wf(nat_of_int(max_length), (tail_chain)(chain, 0));
    }
}

@*/
