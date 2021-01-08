//@ #include <nat.gh>
//@ #include <quantifiers.gh>

/*@

fixpoint fixpoint(a, b) fix__aux<a, b>(fixpoint(fixpoint(a, b), a, b) def, nat n) {
    switch (n) {
        case zero: return (def)(default_value);
        case succ(n0): return (def)(fix__aux(def, n0));
    }
}

fixpoint b fix_<a, b>(fixpoint(fixpoint(a, b), a, b) def, fixpoint(a, int) measure, a x) {
    return (fix__aux)(def, nat_of_int(measure(x)))(x);
}

fixpoint bool eq_lt<a, b>(fixpoint(a, int) measure, fixpoint(a, b) f1, fixpoint(a, b) f2, int m, a x) {
    return measure(x) < 0 || m <= measure(x) || f1(x) == f2(x);
}

fixpoint bool rec_wf_at<a, b>(fixpoint(fixpoint(a, bool), bool) forall_a, fixpoint(fixpoint(a, b), a, b) def, fixpoint(a, int) measure, pair<pair<fixpoint(a, b), fixpoint(a, b)>, a> case_) {
    return !forall_a((eq_lt)(measure, fst(fst(case_)), snd(fst(case_)), measure(snd(case_)))) || measure(snd(case_)) < 0 || def(fst(fst(case_)), snd(case_)) == def(snd(fst(case_)), snd(case_));
}

lemma void fix_unfold_<a, b>(fixpoint(fixpoint(a, b), a, b) def, fixpoint(a, int) measure, a x)
    requires 0 <= measure(x) && fix_(def, measure, x) != def((fix_)(def, measure), x);
    ensures
        exists<pair<pair<fixpoint(a, b), fixpoint(a, b)>, a> >(pair(pair(?f1, ?f2), ?a)) &*&
        [_]is_forall_t<a>(?forall_a) &*& forall_a((eq_lt)(measure, f1, f2, measure(a))) == true &*&
        0 <= measure(a) &*&
        def(f1, a) != def(f2, a);
{
    get_forall_t<pair<pair<fixpoint(a, b), fixpoint(a, b)>, a> >();
    assert [_]is_forall_t(?forall_cases);
    get_forall_t<a>();
    assert [_]is_forall_t(?forall_a);
    if (forall_cases((rec_wf_at)(forall_a, def, measure))) {
        {
            lemma void iter(nat m, nat n, a x1)
                requires [_]is_forall_t<a>(forall_a) &*& [_]is_forall_t(forall_cases) &*& 0 <= measure(x1) && measure(x1) <= int_of_nat(m) && int_of_nat(m) <= int_of_nat(n);
                ensures (fix__aux)(def, m)(x1) == (fix__aux)(def, n)(x1);
            {
                switch (n) {
                    case zero:
                        
                    case succ(n0):
                        switch (m) {
                            case zero:
                                assert measure(x1) == 0;
                                if (!forall_a((eq_lt)(measure, default_value, fix__aux(def, n0), 0))) {
                                    a x2 = not_forall_t(forall_a, (eq_lt)(measure, default_value, fix__aux(def, n0), 0));
                                    assert false;
                                }
                                forall_t_elim(forall_cases, (rec_wf_at)(forall_a, def, measure), pair(pair(default_value<fixpoint(a, b)>, fix__aux(def, n0)), x1));
                            case succ(m0):
                                if (!forall_a((eq_lt)(measure, fix__aux(def, m0), fix__aux(def, n0), measure(x1)))) {
                                    a x2 = not_forall_t(forall_a, (eq_lt)(measure, fix__aux(def, m0), fix__aux(def, n0), measure(x1)));
                                    iter(m0, n0, x2);
                                    assert false;
                                }
                                forall_t_elim(forall_cases, (rec_wf_at)(forall_a, def, measure), pair(pair(fix__aux(def, m0), fix__aux(def, n0)), x1));
                        }
                }
            }
            
            switch (nat_of_int(measure(x))) {
                case zero:
                    if (0 <= measure(x))
                        int_of_nat_of_int(measure(x));
                    if (!forall_a((eq_lt)(measure, default_value, (fix_)(def, measure), 0))) {
                        a x2 = not_forall_t(forall_a, (eq_lt)(measure, default_value, (fix_)(def, measure), 0));
                        assert false;
                    }
                    forall_t_elim(forall_cases, (rec_wf_at)(forall_a, def, measure), pair(pair(default_value<fixpoint(a, b)>, (fix_)(def, measure)), x));
                case succ(n0):
                    if (!forall_a((eq_lt)(measure, fix__aux(def, n0), (fix_)(def, measure), measure(x)))) {
                        a x2 = not_forall_t(forall_a, (eq_lt)(measure, fix__aux(def, n0), (fix_)(def, measure), measure(x)));
                        assert 0 <= measure(x2) && measure(x2) < measure(x) && (fix__aux)(def, n0)(x2) != fix_(def, measure, x2);
                        assert fix_(def, measure, x2) == (fix__aux)(def, nat_of_int(measure(x2)))(x2);
                        int_of_nat_of_int(measure(x) - 1);
                        succ_int(measure(x) - 1);
                        assert measure(x2) <= int_of_nat(n0);
                        iter(nat_of_int(measure(x2)), n0, x2);
                        assert false;
                    }
                    forall_t_elim(forall_cases, (rec_wf_at)(forall_a, def, measure), pair(pair(fix__aux(def, n0), (fix_)(def, measure)), x));
            }
        }
    } else {
        pair<pair<fixpoint(a, b), fixpoint(a, b)>, a> witness = not_forall_t(forall_cases, (rec_wf_at)(forall_a, def, measure));
        close exists(witness);
    }
}

@*/
