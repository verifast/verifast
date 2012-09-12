//@ #include "dlset.gh"
/*@ 


lemma void dlset_remove_contains<t>(list<t> s, t el, t el2)
    requires isDlset(s) == true;
    ensures lset_contains(dlset_remove(s, el), el2) == (el != el2 && lset_contains(s, el2));
{
    switch(s) {
        case nil:
        case cons(h, t): dlset_remove_contains(t, el, el2);
    }
}

lemma void dlset_add_contains<t>(list<t> s, t v, t v2)
    requires isDlset(s) == true;
    ensures lset_contains(dlset_add(s, v), v2) == (v == v2 || lset_contains(s, v2));
{
    dlset_remove_contains(s, v, v2);
}

lemma void lset_empty_isDlset<t>()
    requires true;
    ensures isDlset(lset_empty()) == true;
{
}

lemma void dlset_remove_isDlset<t>(list<t> s, t v)
    requires isDlset(s) == true;
    ensures isDlset(dlset_remove(s, v)) == true;
{
    switch(s) {
        case nil:
        case cons(h, t): 
            if(h != v) dlset_remove_isDlset(t, v);
            dlset_remove_contains(t, v, h);
    } 
}

lemma void dlset_add_isDlset<t>(list<t> s, t v)
    requires isDlset(s) == true;
    ensures isDlset(dlset_add(s, v)) == true;
{
    dlset_remove_contains(s, v, v);
    dlset_remove_isDlset(s, v);
}

lemma void lset_singleton_isDlset<t>(t v)
    requires true;
    ensures isDlset(lset_singleton(v)) == true;    
{
}

lemma void lset_inters_isDlset<t>(list<t> s1, list<t> s2)
    requires isDlset(s1) == true &*& isDlset(s2) == true;
    ensures isDlset(lset_inters(s1, s2)) == true;
{
    switch(s1) {
        case nil:
        case cons(h, t): 
            lset_inters_contains(t, s2, h);
            lset_inters_isDlset(t, s2);
    }
}

lemma void lset_diff_isDlset<t>(list<t> s1, list<t> s2)
    requires isDlset(s1) == true &*& isDlset(s2) == true;
    ensures isDlset(lset_diff(s1, s2)) == true;
{
    switch(s1) {
        case nil:
        case cons(h, t): 
            lset_diff_contains(t, s2, h);
            lset_diff_isDlset(t, s2);
    }
}


lemma void dlset_union_contains<t>(list<t> s1, list<t> s2, t el)
    requires isDlset(s1) == true &*& isDlset(s2) == true;
    ensures lset_contains(dlset_union(s1, s2), el) == (lset_contains(s1, el) || lset_contains(s2, el));
{
    switch(s1) {
        case nil:
        case cons(h, t): 
            dlset_remove_isDlset(s2, h);
            dlset_remove_contains(s2, h, el);
            dlset_union_contains(t, dlset_remove(s2, h), el);
    }
}

lemma void dlset_union_isDlset<t>(list<t> s1, list<t> s2)
    requires isDlset(s1) == true &*& isDlset(s2) == true;
    ensures isDlset(dlset_union(s1, s2)) == true;
{
    switch(s1) {
        case nil:
        case cons(h, t): 
            dlset_remove_isDlset(s2, h);
            dlset_union_isDlset(t, dlset_remove(s2, h));
            dlset_remove_contains(s2, h, h);
            dlset_union_contains(t, dlset_remove(s2, h), h);
    }    
}

lemma void dlset_normalize_helper_spec<t>(list<t> s, list<t> acc, list<t> p) 
    requires isDlset(acc) == true &*& lset_equals(acc, p) == true;
    ensures isDlset(dlset_normalize_helper(s, acc)) == true &*& lset_equals(dlset_normalize_helper(s, acc), append(p, s)) == true;
{
    switch(s) {
        case nil:
        case cons(h, t): 
            if(!lset_equals(lset_contains(acc, h) ? acc : snoc(acc, h), snoc(p, h))) {
                 lset_equals_contains_conv(lset_contains(acc, h) ? acc : snoc(acc, h), snoc(p, h));
                 open exwitness(?v);
                 lset_equals_contains(acc, p, v);
                 lset_union_contains(p, lset_singleton(h), v);
                 lset_union_contains(acc, lset_singleton(h), v);
                 assert false;
            }
            lset_union_contains(acc, lset_singleton(h), h);
            if(!lset_contains(acc, h)) distinct_snoc(acc, h);
            dlset_normalize_helper_spec(t, lset_contains(acc, h) ? acc : snoc(acc, h), snoc(p, h));
            append_cons_r_snoc_l(p, h, t);
    }    
}

lemma void dlset_normalize_isDlset<t>(list<t> s)
    requires true;
    ensures isDlset(dlset_normalize(s))==true;
{
    dlset_normalize_helper_spec(s, nil, nil);
}

lemma void dlset_normalize_equals<t>(list<t> s)
    requires true;
    ensures lset_equals(dlset_normalize(s), s)==true;
{
    dlset_normalize_helper_spec(s, nil, nil);
}

@*/