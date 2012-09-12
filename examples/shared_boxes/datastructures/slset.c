//@ #include "slset.gh"
/*@ 

lemma void slset_empty_contains<t>(t v)
    requires true; 
    ensures !lset_contains(slset_empty(), v);
{
}

lemma void slset_add_contains<t>(list<t> s, t v, t v2, fixpoint (t, t, bool) lt)
    requires true;
    ensures lset_contains(slset_add(s, lt, v), v2) == (v == v2 || lset_contains(s, v2));
{
    switch(s) {
        case nil:
        case cons(h, t):
            slset_add_contains(t, v, v2, lt);
    }
}


lemma void slset_isDlset<t>(list<t> s, fixpoint (t, t, bool) lt, lttrans* translem, ltirrefl* irrefllem)
    requires isSlset(s, lt) == true &*& is_lttrans(translem, lt) &*& is_ltirrefl(irrefllem, lt);
    ensures isDlset(s) == true &*& is_lttrans(translem, lt) &*& is_ltirrefl(irrefllem, lt);
{
    switch(s) {
        case nil:
        case cons(h, t):
            sorted_tail_cons(h, t, lt);
            slset_isDlset(t, lt, translem, irrefllem);
            if(lset_contains(t, h)) {
                sorted_head_min(h, t, h, lt, translem);
                irrefllem(h);
                assert false;
            }
    }
}

lemma void slset_remove_contains<t>(list<t> s, t el, t el2, fixpoint (t, t, bool) lt, lttrans* translem, ltirrefl* irrefllem)
    requires isSlset(s, lt) == true &*& is_lttrans(translem, lt) &*& is_ltirrefl(irrefllem, lt);
    ensures lset_contains(slset_remove(s, el), el2) == (el != el2 && lset_contains(s, el2)) &*& is_lttrans(translem, lt) &*& is_ltirrefl(irrefllem, lt);
{
    slset_isDlset(s, lt, translem, irrefllem);
    dlset_remove_contains(s, el, el2); 
}

lemma void slset_singleton_contains<t>(t v, t v2)
    requires true; 
    ensures lset_contains(slset_singleton(v), v2) == (v == v2);
{
}

lemma void slset_union_contains<t>(list<t> s1, list<t> s2, t el, fixpoint (t, t, bool) lt)
    requires true;
    ensures lset_contains(slset_union(s1, s2, lt), el) == (lset_contains(s1, el) || lset_contains(s2, el));
{
    switch(s2) {
        case nil:
        case cons(h, t):
            slset_union_contains(slset_add(s1, lt, h), t, el, lt);
            slset_add_contains(s1, h, el, lt);
    }
}

lemma void slset_inters_contains<t>(list<t> s1, list<t> s2, t el)
    requires true;
    ensures lset_contains(slset_inters(s1, s2), el) == (lset_contains(s1, el) && lset_contains(s2, el));
{
    lset_inters_contains(s1, s2, el);
}

lemma void slset_diff_contains<t>(list<t> s1, list<t> s2, t el)
    requires true;
    ensures lset_contains(slset_diff(s1, s2), el) == (lset_contains(s1, el) && !lset_contains(s2, el));
{
    lset_diff_contains(s1, s2, el);
}


lemma void slset_empty_isSlset<t>(fixpoint (t, t, bool) lt)
    requires true; 
    ensures isSlset(slset_empty(), lt) == true;
{
}

lemma void slset_add_isSlset<t>(list<t> s, t v, fixpoint (t, t, bool) lt, lttotal* totallem)
    requires isSlset(s, lt) == true &*& is_lttotal(totallem, lt);
    ensures isSlset(slset_add(s, lt, v), lt) == true &*& is_lttotal(totallem, lt);
{
    sorted_insert_sorted(s, lt, v, totallem);
}

lemma void slset_remove_isSlset<t>(list<t> s, t el, fixpoint (t, t, bool) lt, lttrans* translem)
    requires isSlset(s, lt) == true &*& is_lttrans(translem, lt);
    ensures isSlset(slset_remove(s, el), lt) == true &*& is_lttrans(translem, lt);
{
    remove_sorted(s, el, lt, translem);
}

lemma void slset_singleton_isSlset<t>(t v, fixpoint (t, t, bool) lt)
    requires true;
    ensures isSlset(slset_singleton(v), lt) == true;
{
}

lemma void slset_union_isSlset<t>(list<t> s1, list<t> s2, fixpoint (t, t, bool) lt, lttotal* totallem)
    requires isSlset(s1, lt) == true &*& is_lttotal(totallem, lt);
    ensures isSlset(slset_union(s1, s2, lt), lt) == true &*& is_lttotal(totallem, lt);
{
    switch(s2) {
        case nil:
        case cons(h, t):
            slset_add_isSlset(s1, h, lt, totallem);
            slset_union_isSlset(slset_add(s1, lt, h), t, lt, totallem);
    }
}

lemma void slset_inters_isSlset<t>(list<t> s1, list<t> s2, fixpoint (t, t, bool) lt, lttrans* translem)
    requires isSlset(s1, lt) == true &*& is_lttrans(translem, lt);
    ensures isSlset(slset_inters(s1, s2), lt) == true &*& is_lttrans(translem, lt);
{
    switch(s1) {
        case nil:
        case cons(h, t):
            sorted_tail_cons(h, t, lt);
            slset_inters_isSlset(t, s2, lt, translem);
            if(lset_contains(s2, h)) {
                switch(slset_inters(t, s2)) { 
                    case nil:
                    case cons(h2, t2):
                        slset_inters_contains(t, s2, h2);
                        sorted_head_min(h, t, h2, lt, translem);
                }
            } 
    }
}

lemma void slset_diff_isSlset<t>(list<t> s1, list<t> s2, fixpoint (t, t, bool) lt, lttrans* translem)
    requires isSlset(s1, lt) == true &*& is_lttrans(translem, lt);
    ensures isSlset(slset_diff(s1, s2), lt) == true &*& is_lttrans(translem, lt);
{
    switch(s1) {
        case nil:
        case cons(h, t):
            sorted_tail_cons(h, t, lt);
            slset_diff_isSlset(t, s2, lt, translem);
            if(!lset_contains(s2, h)) {
                switch(slset_diff(t, s2)) { 
                    case nil:
                    case cons(h2, t2):
                        slset_diff_contains(t, s2, h2);
                        sorted_head_min(h, t, h2, lt, translem);
                }
            } 
    }
}



@*/