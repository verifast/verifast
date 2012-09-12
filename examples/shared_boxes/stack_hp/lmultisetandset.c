//@ #include "lmultisetandset.gh"

/*@

lemma void lmultiset_occ_lset_contains<t>(list<t> s, t v)
    requires true; 
    ensures lset_contains(s, v) == (lmultiset_occ(s, v) > 0);
{
    occ_mem_full(s, v);
}
lemma void lmultiset_submultiset_lset_subset<t>(list<t> s1, list<t> s2)
    requires true;
    ensures lmultiset_submultiset(s1, s2) ? lset_subset(s1, s2) == true : true ;
{
    if(lmultiset_submultiset(s1, s2) && !lset_subset(s1, s2)) {
        lset_subset_contains_conv(s1, s2);
        open exwitness(?x);
        lmultiset_submultiset_occ(s1, s2, x);
        lmultiset_occ_lset_contains(s1, x);
        lmultiset_occ_lset_contains(s2, x);
        assert false;
    }
}


lemma void lmultiset_equals_lset_equals<t>(list<t> s1, list<t> s2)
    requires true;
    ensures lmultiset_equals(s1, s2) ? lset_equals(s1, s2) == true : true ;
{
    lmultiset_submultiset_lset_subset(s1, s2);
    lmultiset_submultiset_lset_subset(s2, s1);
}


lemma void lmultiset_occ_distinct<t>(list<t> s, t v)
    requires distinct(s) == true;
    ensures lmultiset_occ(s, v) <= 1;
{
    switch(s) {
        case nil:
        case cons(h,t):
            if(h == v) occ_mem_full(t, h);
            lmultiset_occ_distinct(t, v);
    }
}

lemma void lmultiset_occ_distinct_conv<t>(list<t> s)
    requires distinct(s) == false;
    ensures exwitness(?x) &*& lmultiset_occ(s, x) > 1;
{
    switch(s) {
        case nil:
        case cons(h,t):
            if(mem(h, t)) {
                close exwitness(h); occ_mem_full(t, h);
            } else {
                lmultiset_occ_distinct_conv(t);
            }
    }
}


lemma void foreach_lmultiset_equals<t>(list<t> l1, list<t> l2)
    requires foreach(l1, ?p) &*& lmultiset_equals(l1, l2) == true;
    ensures foreach(l2, p);
{
    switch(l1) {
        case nil:
            switch(l2) {
                case nil:
                case cons(h2, t2):
                    lmultiset_equals_occ(l1, l2, h2);
            }
            
        case cons(h,t):
            open foreach(l1, p);
            if(!lmultiset_equals(t, lmultiset_remove(l2, h))) {
                lmultiset_equals_occ_conv(t, lmultiset_remove(l2, h));
                open exwitness(?x);
                lmultiset_remove_occ(l2, h, x);
                lmultiset_equals_occ(l1, l2, x);
                assert false;
            }
            foreach_lmultiset_equals(t, lmultiset_remove(l2, h));
            
            lmultiset_equals_occ(l1, l2, h);
            lmultiset_occ_lset_contains(l2, h);
            foreach_unremove(h, l2);
    }
}

@*/