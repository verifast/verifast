//@ #include <quantifiers.gh>
#include "busywaiting.h"

/*@

fixpoint bool chain_descends_at(fixpoint(int, list<int>) chain, int i) {
    return i < 0 || lexprod_lt(chain(i + 1), chain(i));
}

fixpoint bool starts_with_from(fixpoint(int, list<int>) chain, int h, int i, int j) {
    return j < i || length(chain(j)) > 0 && head(chain(j)) == h;
}

fixpoint list<int> tail_chain(fixpoint(int, list<int>) chain, int i, int j) {
    return tail(chain(i + j));
}

lemma void chain_descends_length_eq(fixpoint(int, list<int>) chain, int i)
    requires forall_int((chain_descends_at)(chain)) == true &*& 0 <= i;
    ensures length(chain(i)) == length(chain(0));
{
    for (int j = 0; j < i; j++)
        invariant 0 <= j && j <= i && length(chain(j)) == length(chain(0));
        decreases i - j;
    {
        forall_int_elim((chain_descends_at)(chain), j);
        lexprod_lt_length_eq(chain(j + 1), chain(j));
    }
}

lemma void lexprod_lt_wf0(nat length, fixpoint(int, list<int>) chain)
    requires length(chain(0)) == int_of_nat(length) && forall_int((chain_descends_at)(chain)) == true;
    ensures false;
{
    switch (length) {
        case zero:
            forall_int_elim((chain_descends_at)(chain), 0);
            lexprod_lt_length_eq(chain(1), chain(0));
            switch (chain(1)) { case nil: case cons(h, t): }
            assert false;
        case succ(length0):
            switch (chain(0)) {
                case nil:
                    assert false;
                case cons(c0h, c0t):
                    int h = c0h;
                    int i = 0;
                    while (0 <= h)
                        invariant 0 <= i &*& chain(i) == cons(h, _);
                        decreases h;
                    {
                        if (forall_int((starts_with_from)(chain, h, i))) {
                            if (!forall_int((chain_descends_at)((tail_chain)(chain, i)))) {
                                int j = not_forall_int((chain_descends_at)((tail_chain)(chain, i)));
                                forall_int_elim((chain_descends_at)(chain), i + j);
                                forall_int_elim((starts_with_from)(chain, h, i), i + j);
                                forall_int_elim((starts_with_from)(chain, h, i), i + j + 1);
                                assert chain(i + j) == cons(?hij, _);
                                assert chain(i + j + 1) == cons(?hij1, _);
                                assert false;
                            }
                            chain_descends_length_eq(chain, i);
                            lexprod_lt_wf0(length0, (tail_chain)(chain, i));
                            assert false;
                        }
                        int i1 = not_forall_int((starts_with_from)(chain, h, i));
                        int newh = 0;
                        while (i < i1)
                            invariant 0 <= i &*& i <= i1 &*& chain(i) == cons(h, _);
                            decreases i1 - i;
                        {
                            if (chain(i + 1) == nil) {
                                forall_int_elim((chain_descends_at)(chain), i + 1);
                                switch (chain(i + 2)) { case nil: case cons(hi2, ti2): }
                                assert false;
                            }
                            assert chain(i + 1) == cons(?h1, _);
                            forall_int_elim((chain_descends_at)(chain), i);
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
                            if (!forall_int((chain_descends_at)((tail_chain)(chain, i)))) {
                                int j = not_forall_int((chain_descends_at)((tail_chain)(chain, i)));
                                forall_int_elim((chain_descends_at)(chain), i + j);
                                forall_int_elim((starts_with_from)(chain, h, i), i + j);
                                forall_int_elim((starts_with_from)(chain, h, i), i + j + 1);
                                assert chain(i + j) == cons(?hij, _);
                                assert chain(i + j + 1) == cons(?hij1, _);
                                assert false;
                            }
                            chain_descends_length_eq(chain, i);
                            lexprod_lt_wf0(length0, (tail_chain)(chain, i));
                            assert false;
                        }
                        int i1 = not_forall_int((starts_with_from)(chain, h, i));
                        while (i < i1)
                            invariant 0 <= i &*& i <= i1 &*& chain(i) == cons(h, _);
                            decreases i1 - i;
                        {
                            if (chain(i + 1) == nil) {
                                forall_int_elim((chain_descends_at)(chain), i + 1);
                                switch (chain(i + 2)) { case nil: case cons(hi2, ti2): }
                                assert false;
                            }
                            assert chain(i + 1) == cons(?h1, _);
                            forall_int_elim((chain_descends_at)(chain), i);
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

lemma void lexprod_lt_wf(fixpoint(int, list<int>) chain)
    requires forall_int((chain_descends_at)(chain)) == true;
    ensures false;
{
    lexprod_lt_wf0(nat_of_int(length(chain(0))), chain);
}

@*/
