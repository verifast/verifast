//@ #include "lmultiset.gh"

/*@

lemma void lmultiset_occ_positive<t>(list<t> s, t v)
    requires true; 
    ensures lmultiset_occ(s, v) >= 0;
{
    switch(s) {
        case nil:
        case cons(h, s2):
            lmultiset_occ_positive(s2, v);
    }
}
lemma void lmultiset_empty_occ<t>(t v)
    requires true; 
    ensures lmultiset_occ(lmultiset_empty(), v) == 0;
{
}

lemma void lmultiset_add_occ<t>(list<t> s, t v, t v2)
    requires true; 
    ensures lmultiset_occ(lmultiset_add(s, v), v2) == lmultiset_occ(s, v2) + (v == v2 ? 1 : 0);
{
}

lemma void lmultiset_remove_occ<t>(list<t> s, t v, t v2)
    requires true;
    ensures lmultiset_occ(lmultiset_remove(s, v), v2) == (v == v2 && lmultiset_occ(s, v2) > 0 ? lmultiset_occ(s, v2) - 1 : lmultiset_occ(s, v2));  
{
    switch(s) {
        case nil:
        case cons(h, s2):
            lmultiset_occ_positive(s2, v2);
            lmultiset_remove_occ(s2, v, v2);
    }
}

lemma void lmultiset_singleton_occ<t>(t v, t v2)
    requires true; 
    ensures lmultiset_occ(lmultiset_singleton(v), v2) == (v == v2 ? 1 : 0);
{
}

lemma void lmultiset_union_occ<t>(list<t> s1, list<t> s2, t el)
    requires true;
    ensures lmultiset_occ(lmultiset_union(s1, s2), el) == lmultiset_occ(s1, el) + lmultiset_occ(s2, el);
{
    switch(s1) {
        case nil:
        case cons(h, s1t):
            lmultiset_union_occ(s1t, s2, el);
    }
}

lemma void lmultiset_inters_occ<t>(list<t> s1, list<t> s2, t el)
    requires true;
    ensures lmultiset_occ(lmultiset_inters(s1, s2), el) == (lmultiset_occ(s1, el) < lmultiset_occ(s2, el) ? lmultiset_occ(s1, el) : lmultiset_occ(s2, el));
{
    switch(s1) {
        case nil:
            lmultiset_occ_positive(s2, el);
        case cons(h, t):
            if(lmultiset_occ(s2, h) > 0) {
                lmultiset_inters_occ(t, lmultiset_remove(s2, h), el);
                lmultiset_remove_occ(s2, h, el);
            } else {
                lmultiset_occ_positive(t, h);
                lmultiset_inters_occ(t, s2, el);
            }            
    }
}

lemma void lmultiset_diff_occ<t>(list<t> s1, list<t> s2, t el)
    requires true;
    ensures lmultiset_occ(lmultiset_diff(s1, s2), el) == (lmultiset_occ(s1, el) > lmultiset_occ(s2, el) ? lmultiset_occ(s1, el) - lmultiset_occ(s2, el) : 0);
{
    switch(s1) {
        case nil:
            lmultiset_occ_positive(s2, el);
        case cons(h, t):
            lmultiset_occ_positive(s2, el);
            lmultiset_remove_occ(s2, h, el);
            if(lmultiset_occ(s2, h) > 0) {
                assert lmultiset_diff(s1, s2) == lmultiset_diff(t, lmultiset_remove(s2, h));
                lmultiset_diff_occ(t, lmultiset_remove(s2, h), el);
                lmultiset_occ_positive(t, h);
            } else {
                assert lmultiset_diff(s1, s2) == cons(h, lmultiset_diff(t, lmultiset_remove(s2, h)));
                lmultiset_diff_occ(t, lmultiset_remove(s2, h), el);
                lmultiset_occ_positive(t, el);
            }            
    }
}

lemma void lmultiset_submultiset_occ<t>(list<t> s1, list<t> s2, t el)
    requires lmultiset_submultiset(s1, s2) == true;
    ensures lmultiset_occ(s1, el) <= lmultiset_occ(s2, el);
{
    switch(s1) {
        case nil:
            lmultiset_occ_positive(s2, el);
        case cons(h, t):
            lmultiset_occ_positive(s2, el);
            assert lmultiset_occ(s2, h) > 0 && lmultiset_submultiset(t, lmultiset_remove(s2, h));
            lmultiset_remove_occ(s2, h, el);
            lmultiset_submultiset_occ(t, lmultiset_remove(s2, h), el);
    } 
}

lemma void lmultiset_equals_occ<t>(list<t> s1, list<t> s2, t el)
    requires lmultiset_equals(s1, s2) == true;
    ensures lmultiset_occ(s1, el) == lmultiset_occ(s2, el);
{
    lmultiset_submultiset_occ(s1, s2, el);
    lmultiset_submultiset_occ(s2, s1, el);
}

lemma void lmultiset_submultiset_occ_conv<t>(list<t> s1, list<t> s2)
    requires lmultiset_submultiset(s1, s2) == false;
    ensures exwitness(?el) &*& lmultiset_occ(s1, el) > lmultiset_occ(s2, el);
{
    switch(s1) {
        case nil:
        case cons(h, t):
        lmultiset_occ_positive(s2, h);
        if(lmultiset_occ(s2, h) > 0) {
            lmultiset_submultiset_occ_conv(t, lmultiset_remove(s2, h));
            assert exwitness(?el);
            lmultiset_remove_occ(s2, h, el);
        } else {
            close exwitness(h);
            lmultiset_occ_positive(t, h);
        }
    }
}

lemma void lmultiset_equals_occ_conv<t>(list<t> s1, list<t> s2)
    requires lmultiset_equals(s1, s2) == false;
    ensures exwitness(?el) &*& lmultiset_occ(s1, el) != lmultiset_occ(s2, el);
{
    if(!lmultiset_submultiset(s1, s2)) lmultiset_submultiset_occ_conv(s1, s2);
    else if(!lmultiset_submultiset(s2, s1)) lmultiset_submultiset_occ_conv(s2, s1);
}

@*/