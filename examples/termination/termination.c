//@ #include "termination.gh"

/*@

lemma t exists_get_witness<t>(list<t> xs, fixpoint(t, bool) p) 
    requires exists(xs, p) == true; 
    ensures mem(result, xs) && p(result); 
{ 
    switch (xs) { 
        case nil: 
        case cons(x0, xs0): 
            if (p(x0)) 
                return x0; 
            else 
                return exists_get_witness(xs0, p); 
    }
}

lemma void exists_not_forall_not<t>(list<t> xs, fixpoint(t, bool) p)
    requires true;
    ensures exists(xs, p) == !forall(xs, (notf)(p));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            exists_not_forall_not(xs0, p);
    }
}

lemma void not_exists<t>(list<t> xs, fixpoint(t, bool) p, t x)
    requires mem(x, xs) && !exists(xs, p);
    ensures !p(x);
{
    exists_not_forall_not(xs, p);
    forall_elim(xs, (notf)(p), x);
}

lemma void exists_intro<t>(t x, list<t> xs, fixpoint(t, bool) p)
    requires mem(x, xs) && p(x);
    ensures exists(xs, p) == true;
{
    if (!exists(xs, p))
        not_exists(xs, p, x);
}

lemma void is_order_antirefl<t>(t x)
    requires [_]is_order<t>(?lt);
    ensures !lt(x, x);
{
    open is_order(lt);
    assert [_]is_forall_t<t>(?forall_t);
    forall_t_elim(forall_t, (is_lt_antirefl_at)(lt), x);
}

// The natural well-founded order on (nonnegative) integers

lemma void is_wf_lt()
    requires true;
    ensures [_]is_wf(lt);
{
    get_forall_t<fixpoint(int, bool)>();
    assert [_]is_forall_t<fixpoint(int, bool)>(?forall_sets);
    get_forall_int();
    if (!forall_sets((has_minimal)(forall_int, lt))) {
        ;
        fixpoint(int, bool) set = not_forall_t<fixpoint(int, bool)>(forall_sets, (has_minimal)(forall_int, lt));
        assert exists_t(forall_int, set) == true;
        int x = not_forall_int((notf)(set));
        assert set(x) == true;
        assert forall_int((notf)((is_minimal)(forall_int, lt, set))) == true;
        for (;;)
            invariant set(x) == true;
            decreases x;
        {
            if (is_minimal(forall_int, lt, set, x)) {
                forall_int_elim((notf)((is_minimal)(forall_int, lt, set)), x);
                assert false;
            } else {
                assert exists_t(forall_int, (is_lesser_element)(set, lt, x)) == true;
                x = not_forall_int((notf)((is_lesser_element)(set, lt, x)));
            }
        }
        assert false;
    }
    close is_wf<int>(lt);
    leak is_wf(lt);
}

// Lexicographic ordering

lemma void note(bool b)
    requires b;
    ensures b;
{
}

fixpoint bool has_pair<a, b>(fixpoint(pair<a, b>, bool) set, a x, b y) { return set(pair(x, y)); }

fixpoint bool fst_set<a, b>(fixpoint(fixpoint(b, bool), bool) forall_b, fixpoint(pair<a, b>, bool) set, a x) {
    return exists_t(forall_b, (has_pair)(set, x));
}

lemma void is_wf_pair_lt<a, b>(fixpoint(a, a, bool) a_lt, fixpoint(b, b, bool) b_lt)
    requires [_]is_wf(a_lt) &*& [_]is_wf(b_lt);
    ensures [_]is_wf((pair_lt)(a_lt, b_lt));
{
    get_forall_t<fixpoint(pair<a, b>, bool)>();
    assert [_]is_forall_t<fixpoint(pair<a, b>, bool)>(?forall_sets);
    get_forall_t<pair<a, b> >();
    assert [_]is_forall_t<pair<a, b> >(?forall_pairs);
    auto forall_a = get_forall_t<a>();
    fixpoint(fixpoint(b, bool), bool) forall_b = get_forall_t<b>();
    fixpoint(pair<a, b>, pair<a, b>, bool) lt = (pair_lt)(a_lt, b_lt);
    if (!forall_sets((has_minimal)(forall_pairs, lt))) {
        ;
        fixpoint(pair<a, b>, bool) set = not_forall_t(forall_sets, (has_minimal)(forall_pairs, lt));
        assert exists_t(forall_pairs, set) == true;
        assert forall_pairs((notf)((is_minimal)(forall_pairs, lt, set))) == true;
        if (!exists_t(forall_a, (fst_set)(forall_b, set))) {
            pair<a, b> p = not_forall_t(forall_pairs, (notf)(set));
            assert set(p) == true;
            assert p == pair(?x, ?y);
            forall_t_elim(forall_a, (notf)((fst_set)(forall_b, set)), x);
            assert !exists_t(forall_b, (has_pair)(set, x));
            forall_t_elim(forall_b, (notf)((has_pair)(set, x)), y);
            assert false;
        }
        assert exists_t(forall_a, (fst_set)(forall_b, set)) == true;
        open is_wf<a>(a_lt);
        assert [_]is_forall_t<fixpoint(a, bool)>(?forall_a_sets);
        forall_t_elim(forall_a_sets, (has_minimal)(forall_a, a_lt), (fst_set)(forall_b, set));
        assert has_minimal(forall_a, a_lt, (fst_set)(forall_b, set)) == true;
        assert exists_t(forall_a, (is_minimal)(forall_a, a_lt, (fst_set)(forall_b, set))) == true;
        a x = not_forall_t(forall_a, (notf)((is_minimal)(forall_a, a_lt, (fst_set)(forall_b, set))));
        assert is_minimal(forall_a, a_lt, (fst_set)(forall_b, set), x) == true;
        assert fst_set(forall_b, set, x) == true;
        assert exists_t(forall_b, (has_pair)(set, x)) == true;
        open is_wf<b>(b_lt);
        assert [_]is_forall_t<fixpoint(b, bool)>(?forall_b_sets);
        forall_t_elim(forall_b_sets, (has_minimal)(forall_b, b_lt), (has_pair)(set, x));
        assert has_minimal(forall_b, b_lt, (has_pair)(set, x)) == true;
        assert exists_t(forall_b, (is_minimal)(forall_b, b_lt, (has_pair)(set, x))) == true;
        b y = not_forall_t(forall_b, (notf)((is_minimal)(forall_b, b_lt, (has_pair)(set, x))));
        assert is_minimal(forall_b, b_lt, (has_pair)(set, x), y) == true;
        assert has_pair(set, x, y) == true;
        if (exists_t(forall_pairs, (is_lesser_element)(set, lt, pair(x, y)))) {
            pair<a, b> p1 = not_forall_t(forall_pairs, (notf)((is_lesser_element)(set, lt, pair(x, y))));
            assert p1 == pair(?x1, ?y1);
            assert is_lesser_element(set, lt, pair(x, y), pair(x1, y1)) == true;
            assert set(pair(x1, y1)) == true;
            assert a_lt(x1, x) || x1 == x && b_lt(y1, y);
            if (a_lt(x1, x)) {
                if (!fst_set(forall_b, set, x1)) {
                    forall_t_elim(forall_b, (notf)((has_pair)(set, x1)), y1);
                    assert false;
                }
                assert is_lesser_element((fst_set)(forall_b, set), a_lt, x, x1) == true;
                forall_t_elim(forall_a, (notf)((is_lesser_element)((fst_set)(forall_b, set), a_lt, x)), x1);
                assert false;
            } else {
                forall_t_elim(forall_b, (notf)((is_lesser_element)((has_pair)(set, x), b_lt, y)), y1);
                assert false;
            }
            assert false;
        }
        assert is_minimal(forall_pairs, lt, set, pair(x, y)) == true;
        forall_t_elim(forall_pairs, (notf)((is_minimal)(forall_pairs, lt, set)), pair(x, y));
        assert false;
    }
    close is_wf<pair<a, b> >((pair_lt)(a_lt, b_lt));
    leak is_wf((pair_lt)(a_lt, b_lt));
}

// Well-founded induction 

lemma void wf_induct<t>(fixpoint(t, t, bool) lt, fixpoint(t, bool) p)
    requires [_]is_wf<t>(lt) &*& is_wf_inductive(lt, p);
    ensures [_]is_forall_t<t>(?forall_t) &*& forall_t(p) == true;
{
    open is_wf<t>(lt);
    open is_wf_inductive(lt, p);
    assert [_]is_forall_t<t>(?forall_t);
    if (!forall_t(p)) {
        t x = not_forall_t(forall_t, p);
        assert [_]is_forall_t<fixpoint(t, bool)>(?forall_sets);
        forall_t_elim(forall_sets, (has_minimal)(forall_t, lt), (notf)(p));
        if (forall_t((notf)((notf)(p)))) {
            forall_t_elim(forall_t, (notf)((notf)(p)), x);
            assert false;
        }
        assert exists_t(forall_t, (is_minimal)(forall_t, lt, (notf)(p))) == true;
        t y = not_forall_t(forall_t, (notf)((is_minimal)(forall_t, lt, (notf)(p))));
        assert !p(y) && !exists_t(forall_t, (is_lesser_element)((notf)(p), lt, y));
        if (!forall_t((implies)((flip)(lt)(y), p))) {
            t z = not_forall_t(forall_t, (implies)((flip)(lt)(y), p));
            assert lt(z, y) && !p(z);
            forall_t_elim(forall_t, (notf)((is_lesser_element)((notf)(p), lt, y)), z);
            assert false;
        }
        forall_t_elim(forall_t, (is_wf_inductive_at)(forall_t, lt, p), y);
        assert false;
    }
}

// func_lt is a partial order

lemma void is_order_func_lt()
    requires true;
    ensures [_]is_order(func_lt);
{
    get_forall_t<pair<void *, pair<void *, void *> > >();
    assert [_]is_forall_t(?forall_triples);
    get_forall_t<void *>();
    assert [_]is_forall_t(?forall_f);
    if (!forall_triples((is_lt_trans_at)(func_lt))) {
        pair<void *, pair<void *, void *> > fgh = not_forall_t(forall_triples, (is_lt_trans_at)(func_lt));
        assert false;
    }
    if (!forall_f((is_lt_antirefl_at)(func_lt))) {
        void *f = not_forall_t(forall_f, (is_lt_antirefl_at)(func_lt));
        assert false;
    }
    close is_order(func_lt);
    leak is_order(func_lt);
}

// Properties of bag_le

lemma void remove_all_xs_xs<t>(list<t> xs)
    requires true;
    ensures remove_all(xs, xs) == nil;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            remove_remove_all(x0, xs0, xs);
            remove_all_xs_xs(xs0);
    }
}

lemma void remove_all_cons_xs_xs<t>(t x, list<t> xs)
    requires true;
    ensures remove_all(cons(x, xs), xs) == nil;
{
    remove_all_xs_xs(xs);
}

lemma void remove_all_xs_cons_xs<t>(t x, list<t> xs)
    requires true;
    ensures remove_all(xs, cons(x, xs)) == {x};
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            remove_remove_all(x0, xs0, cons(x, xs));
            if (x0 == x) {
            } else {
            }
            remove_all_xs_cons_xs(x, xs0);
    }
}

lemma void bag_lt_cons_lt<t>(fixpoint(t, t, bool) lt, t x, t y, list<t> xs)
    requires [_]is_order(lt) &*& lt(x, y) == true;
    ensures bag_lt(lt, cons(x, xs), cons(y, xs)) == true;
{
    is_order_antirefl(x);
    remove_all_xs_cons_xs(x, xs);
    assert remove_all(cons(y, xs), cons(x, xs)) == {x};
    remove_all_xs_cons_xs(y, xs);
    assert remove_all(cons(x, xs), cons(y, xs)) == {y};
    assert all_lt_some(lt, remove_all(cons(y, xs), cons(x, xs)), remove_all(cons(x, xs), cons(y, xs))) == true;
    assert bag_le(lt, cons(x, xs), cons(y, xs)) == true;
    assert remove_all(cons(y, xs), cons(x, xs)) != nil;
}

lemma void bag_lt_xs_cons_xs<t>(fixpoint(t, t, bool) lt, t x, list<t> xs)
    requires true;
    ensures bag_lt(lt, xs, cons(x, xs)) == true;
{
    remove_all_cons_xs_xs(x, xs);
    assert all_lt_some(lt, remove_all(cons(x, xs), xs), remove_all(xs, cons(x, xs))) == true;
    remove_all_xs_cons_xs(x, xs);
}

lemma void not_mem_remove<t>(t x, list<t> xs)
    requires !mem(x, xs);
    ensures remove(x, xs) == xs;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            not_mem_remove(x, xs0);
    }
}

lemma void count_eq_remove_all<t>(t z, list<t> xs, list<t> ys)
    requires true;
    ensures count_eq(z, remove_all(xs, ys)) == max_(0, count_eq(z, ys) - count_eq(z, xs));
{
    switch (xs) {
        case nil:
            count_nonnegative(ys, (eq)(z));
        case cons(x, xs0):
            count_eq_remove_all(z, xs0, ys);
            if (mem(x, remove_all(xs0, ys))) {
                count_remove(remove_all(xs0, ys), (eq)(z), x);
                count_nonnegative(remove_all(xs, ys), (eq)(z));
            } else {
                not_mem_remove(x, remove_all(xs0, ys));
                if (x == z) {
                    if (count_eq(z, remove_all(xs0, ys)) != 0) {
                        count_non_zero(remove_all(xs0, ys), (eq)(z));
                        assert false;
                    }
                }
            }
    }
}

lemma void mem_count_eq<t>(t x, list<t> xs)
    requires true;
    ensures mem(x, xs) == (count_eq(x, xs) > 0);
{
    count_nonnegative(xs, (eq)(x));
    if (mem(x, xs)) {
        if (count_eq(x, xs) == 0)
            count_zero_mem(xs, (eq)(x), x);
    } else {
        if (count_eq(x, xs) != 0)
            count_non_zero(xs, (eq)(x));
    }
}

lemma void mem_remove_all_count_eq<t>(t z, list<t> xs, list<t> ys)
    requires true;
    ensures mem(z, remove_all(xs, ys)) == (count_eq(z, ys) > count_eq(z, xs));
{
    mem_count_eq(z, remove_all(xs, ys));
    count_eq_remove_all(z, xs, ys);
}

lemma void mem_remove_all_append_l_commut<t>(t x, list<t> xs, list<t> ys, list<t> zs)
    requires true;
    ensures mem(x, remove_all(append(xs, ys), zs)) == mem(x, remove_all(append(ys, xs), zs));
{
    mem_remove_all_count_eq(x, append(xs, ys), zs);
    mem_remove_all_count_eq(x, append(ys, xs), zs);
    count_append(xs, ys, (eq)(x));
    count_append(ys, xs, (eq)(x));
}

lemma void mem_remove_all_append_r_commut<t>(t x, list<t> xs, list<t> ys, list<t> zs)
    requires true;
    ensures mem(x, remove_all(zs, append(xs, ys))) == mem(x, remove_all(zs, append(ys, xs)));
{
    mem_remove_all_count_eq(x, zs, append(xs, ys));
    mem_remove_all_count_eq(x, zs, append(ys, xs));
    count_append(xs, ys, (eq)(x));
    count_append(ys, xs, (eq)(x));
}

lemma void remove_all_append_xs_append_xs<t>(list<t> xs, list<t> ys, list<t> zs)
    requires true;
    ensures remove_all(append(xs, ys), append(xs, zs)) == remove_all(ys, zs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            remove_remove_all(x0, append(xs0, ys), append(xs, zs));
            remove_all_append_xs_append_xs(xs0, ys, zs);
    }
}

lemma void bag_le_append_r<t>(fixpoint(t, t, bool) lt, list<t> xs, list<t> ys)
    requires true;
    ensures bag_le(lt, ys, append(xs, ys)) == true;
{
    switch (remove_all(append(xs, ys), ys)) {
        case nil:
        case cons(x, xs0):
            mem_remove_all_count_eq(x, append(xs, ys), ys);
            count_append(xs, ys, (eq)(x));
            assert count_eq(x, xs) + count_eq(x, ys) < count_eq(x, ys);
            count_nonnegative(xs, (eq)(x));
            assert false;
    }
}

lemma void bag_le_cons_xs_cons_ys<t>(fixpoint(t, t, bool) lt, t x, list<t> xs, list<t> ys)
    requires bag_le(lt, xs, ys) == true;
    ensures bag_le(lt, cons(x, xs), cons(x, ys)) == true;
{
    remove_remove_all(x, ys, cons(x, xs));
    assert remove_all(cons(x, ys), cons(x, xs)) == remove_all(ys, xs);
    remove_remove_all(x, xs, cons(x, ys));
}

lemma void bag_le_bag_le_append_l<t>(fixpoint(t, t, bool) lt, list<t> xs1, list<t> xs2, list<t> ys)
    requires bag_le(lt, xs1, xs2) == true;
    ensures bag_le(lt, append(xs1, ys), append(xs2, ys)) == true;
{
    if (!forall(remove_all(append(xs2, ys), append(xs1, ys)), (lt_some)(lt, remove_all(append(xs1, ys), append(xs2, ys))))) {
        t x = not_forall(remove_all(append(xs2, ys), append(xs1, ys)), (lt_some)(lt, remove_all(append(xs1, ys), append(xs2, ys))));
        assert mem(x, remove_all(append(xs2, ys), append(xs1, ys))) == true;
        mem_remove_all_append_l_commut(x, xs2, ys, append(xs1, ys));
        assert mem(x, remove_all(append(ys, xs2), append(xs1, ys))) == true;
        mem_remove_all_append_r_commut(x, xs1, ys, append(ys, xs2));
        assert mem(x, remove_all(append(ys, xs2), append(ys, xs1))) == true;
        remove_all_append_xs_append_xs(ys, xs2, xs1);
        assert mem(x, remove_all(xs2, xs1)) == true;
        forall_elim(remove_all(xs2, xs1), (lt_some)(lt, remove_all(xs1, xs2)), x);
        assert exists(remove_all(xs1, xs2), (lt)(x)) == true;
        t y = exists_get_witness(remove_all(xs1, xs2), (lt)(x));
        assert mem(y, remove_all(xs1, xs2)) == true;
        remove_all_append_xs_append_xs(ys, xs1, xs2);
        assert mem(y, remove_all(append(ys, xs1), append(ys, xs2))) == true;
        mem_remove_all_append_r_commut(y, xs2, ys, append(ys, xs1));
        assert mem(y, remove_all(append(ys, xs1), append(xs2, ys))) == true;
        mem_remove_all_append_l_commut(y, ys, xs1, append(xs2, ys));
        assert mem(y, remove_all(append(xs1, ys), append(xs2, ys))) == true;
        exists_intro(y, remove_all(append(xs1, ys), append(xs2, ys)), (lt)(x));
        assert false;
    }
}
lemma void le_lt_trans<t>(fixpoint(t, t, bool) lt, t x, t y, t z)
    requires [_]is_order(lt) &*& le(lt, x, y) && lt(y, z);
    ensures lt(x, z) == true;
{
    if (x != y) {
        open [_]is_order(lt);
        assert [_]is_forall_t<pair<t, pair<t, t> > >(?forall_triples);
        forall_t_elim(forall_triples, (is_lt_trans_at)(lt), pair(x, pair(y, z)));
    }
}

lemma void implies_count_le<t>(list<t> xs, fixpoint(t, bool) p1, fixpoint(t, bool) p2)
    requires [_]is_forall_t<t>(?forall_t) &*& forall_t((implies_at)(p2, p1)) == true;
    ensures count(xs, p2) <= count(xs, p1);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            forall_t_elim(forall_t, (implies_at)(p2, p1), x0);
            implies_count_le(xs0, p1, p2);
    }
}

lemma void mem_count_decreases<t>(t x, list<t> xs, fixpoint(t, bool) p1, fixpoint(t, bool) p2)
    requires [_]is_forall_t<t>(?forall_t) &*& mem(x, xs) && p1(x) && !p2(x) && forall_t((implies_at)(p2, p1));
    ensures count(xs, p2) < count(xs, p1);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
                implies_count_le(xs0, p1, p2);
            } else {
                forall_t_elim(forall_t, (implies_at)(p2, p1), x0);
                mem_count_decreases(x, xs0, p1, p2);
            }
    }
}

lemma void lt_forall_t_implies_at<t>(fixpoint(t, t, bool) lt, t x, t y)
    requires [_]is_order(lt) &*& lt(x, y) == true;
    ensures [_]is_forall_t<t>(?forall_t) &*& forall_t((implies_at)((lt)(y), (lt)(x))) == true;
{
    fixpoint(fixpoint(t, bool), bool) forall_t = get_forall_t<t>();
    if (!forall_t((implies_at)((lt)(y), (lt)(x)))) {
        t z = not_forall_t(forall_t, (implies_at)((lt)(y), (lt)(x)));
        assert lt(y, z) && !lt(x, z);
        open [_]is_order(lt);
        assert [_]is_forall_t<pair<t, pair<t, t> > >(?forall_triples);
        forall_t_elim(forall_triples, (is_lt_trans_at)(lt), pair(x, pair(y, z)));
    }
}

lemma void mem_remove_all_trans<t>(t x, list<t> xs, list<t> ys, list<t> zs)
    requires mem(x, remove_all(ys, xs)) && !mem(x, remove_all(zs, xs));
    ensures mem(x, remove_all(ys, zs)) == true;
{
    mem_remove_all_count_eq(x, ys, xs);
    mem_remove_all_count_eq(x, zs, xs);
    mem_remove_all_count_eq(x, ys, zs);
}

lemma void bag_le_trans<t>(fixpoint(t, t, bool) lt, list<t> xs, list<t> ys, list<t> zs)
    requires [_]is_order(lt) &*& bag_le(lt, xs, ys) && bag_le(lt, ys, zs);
    ensures bag_le(lt, xs, zs) == true;
{
    if (!forall(remove_all(zs, xs), (lt_some)(lt, remove_all(xs, zs)))) {
        t x0 = not_forall(remove_all(zs, xs), (lt_some)(lt, remove_all(xs, zs)));
        t x = x0;
        assert !exists(remove_all(xs, zs), (lt)(x0));
        if (!mem(x, remove_all(ys, xs))) {
            mem_remove_all_count_eq(x, zs, xs);
            mem_remove_all_count_eq(x, ys, xs);
            mem_remove_all_count_eq(x, zs, ys);
            assert mem(x, remove_all(zs, ys)) == true;
        }
        for (;;)
            invariant [_]is_order(lt) &*& mem(x, remove_all(ys, xs)) || mem(x, remove_all(zs, ys)) &*& le(lt, x0, x) == true;
            decreases count(remove_all(ys, xs), (lt)(x)) + count(remove_all(zs, ys), (lt)(x));
        {
            if (mem(x, remove_all(ys, xs))) {
                forall_elim(remove_all(ys, xs), (lt_some)(lt, remove_all(xs, ys)), x);
                assert exists(remove_all(xs, ys), (lt)(x)) == true;
                t y = exists_get_witness(remove_all(xs, ys), (lt)(x));
                le_lt_trans(lt, x0, x, y);
                assert lt(x0, y) == true;
                if (mem(y, remove_all(zs, ys))) {
                    lt_forall_t_implies_at(lt, x, y);
                    implies_count_le(remove_all(ys, xs), (lt)(x), (lt)(y));
                    assert count(remove_all(ys, xs), (lt)(y)) <= count(remove_all(ys, xs), (lt)(x));
                    is_order_antirefl(y);
                    mem_count_decreases(y, remove_all(zs, ys), (lt)(x), (lt)(y));
                    assert count(remove_all(zs, ys), (lt)(y)) < count(remove_all(zs, ys), (lt)(x));
                    count_nonnegative(remove_all(ys, xs), (lt)(y));
                    count_nonnegative(remove_all(zs, ys), (lt)(y));
                    x = y;
                } else {
                    mem_remove_all_trans(y, ys, xs, zs);
                    assert mem(y, remove_all(xs, zs)) == true;
                    assert !exists(remove_all(xs, zs), (lt)(x0));
                    not_exists(remove_all(xs, zs), (lt)(x0), y);
                    assert false;
                }
            } else {
                forall_elim(remove_all(zs, ys), (lt_some)(lt, remove_all(ys, zs)), x);
                t z = exists_get_witness(remove_all(ys, zs), (lt)(x));
                le_lt_trans(lt, x0, x, z);
                assert lt(x0, z) == true;
                if (mem(z, remove_all(xs, zs))) {
                    not_exists(remove_all(xs, zs), (lt)(x0), z);
                    assert false;
                } else {
                    mem_remove_all_trans(z, zs, ys, xs);
                    assert mem(z, remove_all(ys, xs)) == true;
                    
                    lt_forall_t_implies_at(lt, x, z);
                    implies_count_le(remove_all(zs, ys), (lt)(x), (lt)(z));
                    assert count(remove_all(zs, ys), (lt)(z)) <= count(remove_all(zs, ys), (lt)(x));
                    is_order_antirefl(z);
                    mem_count_decreases(z, remove_all(ys, xs), (lt)(x), (lt)(z));
                    assert count(remove_all(ys, xs), (lt)(z)) < count(remove_all(ys, xs), (lt)(x));
                    count_nonnegative(remove_all(zs, ys), (lt)(z));
                    count_nonnegative(remove_all(ys, xs), (lt)(z));
                    x = z;
                }
            }
        }
    }
}

lemma void bag_le_bag_lt<t>(fixpoint(t, t, bool) lt, list<t> xs, list<t> ys, list<t> zs)
    requires [_]is_order(lt) &*& bag_le(lt, xs, ys) && bag_lt(lt, ys, zs);
    ensures bag_lt(lt, xs, zs) == true;
{
    bag_le_trans(lt, xs, ys, zs);
    assert remove_all(ys, zs) != nil;
    assert remove_all(ys, zs) == cons(?z, _);
    for (;;)
        invariant [_]is_order(lt) &*& mem(z, remove_all(ys, zs)) == true;
        decreases count(remove_all(ys, zs), (lt)(z));
    {
        if (mem(z, remove_all(xs, zs)))
            break;
        mem_remove_all_trans(z, zs, ys, xs);
        assert mem(z, remove_all(ys, xs)) == true;
        forall_elim(remove_all(ys, xs), (lt_some)(lt, remove_all(xs, ys)), z);
        t y = exists_get_witness(remove_all(xs, ys), (lt)(z));
        if (mem(y, remove_all(zs, ys))) {
            forall_elim(remove_all(zs, ys), (lt_some)(lt, remove_all(ys, zs)), y);
            t z1 = exists_get_witness(remove_all(ys, zs), (lt)(y));
            le_lt_trans(lt, z, y, z1);
            lt_forall_t_implies_at(lt, z, z1);
            is_order_antirefl(z1);
            mem_count_decreases(z1, remove_all(ys, zs), (lt)(z), (lt)(z1));
            assert count(remove_all(ys, zs), (lt)(z1)) < count(remove_all(ys, zs), (lt)(z));
            count_nonnegative(remove_all(ys, zs), (lt)(z));
            z = z1;
        } else {
            mem_remove_all_trans(y, ys, xs, zs);
            assert mem(y, remove_all(xs, zs)) == true;
            break;
        }
    }
    switch (remove_all(xs, zs)) { case nil: case cons(h, t): }
    assert remove_all(xs, zs) != nil;
}

@*/
