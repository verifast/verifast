//@ #include "almap.gh"

/*@


// lemma's about basic inspectors

lemma void almap_get_entry_key<te,tk>(list<te> es, fixpoint(te, tk) fk, tk k)
    requires almap_contains_key(es, fk, k) == true;
    ensures fk(almap_get_entry(es, fk, k)) == k;
{
    switch(es) {
        case nil:
        case cons(e, es2): if(fk(e)!=k) almap_get_entry_key(es2, fk, k);
    }
}


//lemma's for derived inspectors

lemma void almap_contains_entry_spec<te,tk>(list<te> es, fixpoint(te, tk) fk, te e)
    requires true;
    ensures almap_contains_entry(es, fk, e) == (almap_contains_key(es, fk, fk(e)) && almap_get_entry(es, fk, fk(e)) == e);
{
}
    
lemma void almap_get_value_spec<te,tk,tv>(list<te> es, fixpoint(te, tk) fk, fixpoint(te, tv) fv, tk k)
    requires true;
    ensures almap_get_value(es, fk, fv, k) == fv(almap_get_entry(es, fk, k));
{
}

lemma void almap_keys_contains_key<te,tk>(list<te> es, fixpoint(te, tk) fk, tk k)
    requires true;
    ensures lset_contains(almap_keys(es, fk), k) == almap_contains_key(es, fk, k);
{
    switch(es) {
        case nil:
        case cons(e, es2):
            almap_keys_contains_key(es2, fk, k);
    }   
}

lemma void almap_override_contains_key<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk, tk k)
    requires true; 
    ensures almap_contains_key(almap_override(es1, es2, fk), fk, k) == (almap_contains_key(es1, fk, k) || almap_contains_key(es2, fk, k));
{
    switch(es1) {
        case nil: 
        case cons(h, t):
            almap_override_contains_key(t, es2, fk, k);
    }
}

lemma void almap_override_contains_entry<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk, te e)
    requires true;
    ensures almap_contains_entry(append(es1, es2), fk, e) == (almap_contains_key(es1, fk, fk(e)) ? almap_contains_entry(es1, fk, e) :  almap_contains_entry(es2, fk, e));
{
    switch(es1) {
        case nil: 
        case cons(h, t):
            almap_override_contains_entry(t, es2, fk, e);
    }
}

lemma void almap_restrict_contains_key<te,tk>(list<te> es, list<tk> ks, fixpoint(te, tk) fk, tk k)
    requires true; 
    ensures almap_contains_key(almap_restrict(es, ks, fk), fk, k) == (lset_contains(ks, k) && almap_contains_key(es, fk, k));
{
    switch(es) {
        case nil: 
        case cons(h, t):
            almap_restrict_contains_key(t, ks, fk, k);
    }
}

lemma void dk_contains_entry_lset_contains<te,tk>(list<te> es, fixpoint(te, tk) fk, te e)
    requires distinct(almap_keys(es, fk)) == true;
    ensures lset_contains(es, e) == almap_contains_entry(es, fk, e);
{
    switch(es) {
        case nil:
        case cons(e2, es2): 
            dk_contains_entry_lset_contains(es2, fk, e);
            almap_keys_contains_key(es2, fk, fk(e));
    }
}

lemma void almap_entries_helper_contains_entry<te,tk>(list<te> es, fixpoint(te, tk) fk, te e, list<te> res)
    requires distinct(almap_keys(res, fk)) == true;
    ensures lset_contains(almap_entries_helper(es, fk, res), e) == almap_contains_entry(append(res, es), fk, e) &*& 
            distinct(almap_keys(almap_entries_helper(es, fk, res), fk)) == true;
{
    switch(es) {
        case nil: dk_contains_entry_lset_contains(res, fk, e);
        case cons(e2, es2):
            if(almap_contains_key(res, fk, fk(e2))) {
                almap_entries_helper_contains_entry(es2, fk, e, res);
                almap_override_contains_entry(res, es, fk, e);
                almap_override_contains_entry(res, es2, fk, e);
            } else {
                map_append(fk, res, cons(e2, nil));
                almap_keys_contains_key(res, fk, fk(e2));
                distinct_snoc(almap_keys(res, fk), fk(e2));
                almap_entries_helper_contains_entry(es2, fk, e, snoc(res, e2));
                append_cons_r_snoc_l(res, e2, es2);
            }
    }
}

lemma void almap_entries_contains_entry<te,tk>(list<te> es, fixpoint(te, tk) fk, te e)
    requires true;
    ensures lset_contains(almap_entries(es, fk), e) == almap_contains_entry(es, fk, e);
{
    almap_entries_helper_contains_entry(es, fk, e, nil);
}

lemma void almap_contains_value_true<te,tk,tv>(list<te> es, fixpoint(te, tk) fk, fixpoint(te, tv) fv, tv v)
    requires almap_contains_value(es, fk, fv, v) == true;
    ensures exwitness(?e) &*& almap_contains_entry(es, fk, e) == true &*& fv(e) == v;
{
    assert almap_contains_value(es, fk, fv, v) == lset_contains(map(fv, almap_entries(es, fk)), v);
    mem_map_true(fv, almap_entries(es, fk), v);
    assert exwitness(?e);
    almap_entries_contains_entry(es, fk, e);
}

lemma void almap_contains_value_false<te,tk,tv>(list<te> es, fixpoint(te, tk) fk, fixpoint(te, tv) fv, tv v, te e)
    requires almap_contains_value(es, fk, fv, v) == false &*& almap_contains_entry(es, fk, e) == true;
    ensures fv(e) != v;
{
    assert almap_contains_value(es, fk, fv, v) == lset_contains(map(fv, almap_entries(es, fk)), v);
    almap_entries_contains_entry(es, fk, e);
    mem_map_false(fv, almap_entries(es, fk), e, v);
}


lemma void almap_values_contains_value<te,tk,tv>(list<te> es, fixpoint(te, tk) fk, fixpoint(te, tv) fv, tv v)
    requires true;
    ensures lset_contains(almap_values(es, fk, fv), v) == almap_contains_value(es, fk, fv, v);
{
}

lemma void almap_disjoint_true<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk, tk k)
    requires almap_disjoint(es1, es2, fk) == true;
    ensures !almap_contains_key(es1, fk, k) || !almap_contains_key(es2, fk, k);
{
    lset_inters_contains(almap_keys(es1, fk), almap_keys(es2, fk), k);
    almap_keys_contains_key(es1, fk, k);
    almap_keys_contains_key(es2, fk, k);    
}

lemma void almap_disjoint_false<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk)
    requires almap_disjoint(es1, es2, fk) == false;
    ensures exwitness(?k) &*& almap_contains_key(es1, fk, k) == true &*& almap_contains_key(es2, fk, k) == true;
{
    switch(lset_inters(almap_keys(es1, fk), almap_keys(es2, fk))) {
        case nil:
        case cons(k, t):
            close exwitness(k);
            lset_inters_contains(almap_keys(es1, fk), almap_keys(es2, fk), k);
            almap_keys_contains_key(es1, fk, k);
            almap_keys_contains_key(es2, fk, k);
    } 
}

// specification of construtors

lemma void almap_empty_contains_entry<te,tk>(list<te> es, fixpoint(te, tk) fk, te e)
    requires true; 
    ensures !almap_contains_entry(almap_empty(), fk, e);  
{
}

lemma void almap_remove_key_contains_entry<te,tk>(list<te> es, fixpoint(te, tk) fk, tk k, te e)
    requires true; 
    ensures almap_contains_entry(almap_remove_key(es, fk, k), fk, e) == (k != fk(e) && almap_contains_entry(es, fk, e)); 
{
    switch(es) {
        case nil:
        case cons(e2, es2):
            almap_remove_key_contains_entry(es2, fk, k, e);
    }
}

lemma void almap_put_contains_entry<te,tk>(list<te> es, fixpoint(te, tk) fk, te e1, te e2)
    requires true; 
    ensures almap_contains_entry(almap_put(es, fk, e1), fk, e2) == (fk(e1) == fk(e2) ? e1 == e2 : almap_contains_entry(es, fk, e2)); 
{
}

lemma void almap_empty_contains_key<te,tk>(list<te> es, fixpoint(te, tk) fk, tk k)
    requires true; 
    ensures !almap_contains_key(almap_empty(), fk, k);  
{
}

lemma void almap_remove_key_contains_key<te,tk>(list<te> es, fixpoint(te, tk) fk, tk k, tk k2)
    requires true; 
    ensures almap_contains_key(almap_remove_key(es, fk, k), fk, k2) == (k != k2 && almap_contains_key(es, fk, k2)); 
{
    switch(es) {
        case nil:
        case cons(e2, es2):
            almap_remove_key_contains_key(es2, fk, k, k2);
    }
}

lemma void almap_put_contains_key<te,tk>(list<te> es, fixpoint(te, tk) fk, te e, tk k)
    requires true; 
    ensures almap_contains_key(almap_put(es, fk, e), fk, k) == (fk(e) == k || almap_contains_key(es, fk, k)); 
{
}


lemma void almap_restrict_contains_entry<te,tk>(list<te> es, list<tk> ks, fixpoint(te, tk) fk, te e)
    requires true; 
    ensures almap_contains_entry(almap_restrict(es, ks, fk), fk, e) == (lset_contains(ks, fk(e)) && almap_contains_entry(es, fk, e));
{
    switch(es) {
        case nil: 
        case cons(h, t):
            almap_restrict_contains_entry(t, ks, fk, e);
    }
    
}


// specification of almap_submap and almap_equals

lemma void almap_submap_contains_entry<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk, te el)
    requires almap_submap(es1, es2, fk) == true;
    ensures almap_contains_entry(es1, fk, el) ? almap_contains_entry(es2, fk, el) == true : true;
{
    almap_entries_contains_entry(es1, fk, el);
    almap_entries_contains_entry(es2, fk, el);
    lset_subset_contains(almap_entries(es1, fk), almap_entries(es2, fk), el);
}

lemma void almap_equals_contains_entry<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk, te el)
    requires almap_equals(es1, es2, fk) == true;
    ensures almap_contains_entry(es1, fk, el) == almap_contains_entry(es2, fk, el);
{
    almap_submap_contains_entry(es1, es2, fk, el);
    almap_submap_contains_entry(es2, es1, fk, el);
}

lemma void almap_submap_contains_key<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk, tk k)
    requires almap_submap(es1, es2, fk) == true;
    ensures almap_contains_key(es1, fk, k) ? almap_contains_key(es2, fk, k) == true : true;
{
    if(almap_contains_key(es1, fk, k)) {
        almap_get_entry_key(es1, fk, k);
        almap_submap_contains_entry(es1, es2, fk, almap_get_entry(es1, fk, k));
    }
}

lemma void almap_equals_contains_key<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk, tk k)
    requires almap_equals(es1, es2, fk) == true;
    ensures almap_contains_key(es1, fk, k) == almap_contains_key(es2, fk, k);
{
    almap_submap_contains_key(es1, es2, fk, k);
    almap_submap_contains_key(es2, es1, fk, k);
}

lemma void almap_submap_contains_entry_conv<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk)
    requires almap_submap(es1, es2, fk) == false;
    ensures exwitness(?el) &*& almap_contains_entry(es1, fk, el) == true &*& !almap_contains_entry(es2, fk, el);
{
    lset_subset_contains_conv(almap_entries(es1, fk), almap_entries(es2, fk));
    assert exwitness(?el);
    almap_entries_contains_entry(es1, fk, el);
    almap_entries_contains_entry(es2, fk, el);
}

lemma void almap_equals_contains_entry_conv<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk)
    requires almap_equals(es1, es2, fk) == false;
    ensures exwitness(?el) &*& almap_contains_entry(es1, fk, el) != almap_contains_entry(es2, fk, el);
{
    lset_equals_contains_conv(almap_entries(es1, fk), almap_entries(es2, fk));
    assert exwitness(?el);
    almap_entries_contains_entry(es1, fk, el);
    almap_entries_contains_entry(es2, fk, el);
}

// misc

lemma void almap_entries_helper_distinct<te,tk>(list<te> es, fixpoint(te, tk) fk, list<te> res)
    requires distinct(almap_keys(res, fk)) == true;
    ensures distinct(almap_keys(almap_entries_helper(es, fk, res), fk)) == true;
{
    switch(es) {
        case nil: 
        case cons(e2, es2):
            if(almap_contains_key(res, fk, fk(e2))) {
                almap_entries_helper_distinct(es2, fk, res);
            } else {
                map_append(fk, res, cons(e2, nil));
                almap_keys_contains_key(res, fk, fk(e2));
                distinct_snoc(almap_keys(res, fk), fk(e2));
                almap_entries_helper_distinct(es2, fk, snoc(res, e2));
                append_cons_r_snoc_l(res, e2, es2);
            }
    }
}

lemma void almap_entries_distinct<te,tk>(list<te> es, fixpoint(te, tk) fk)
    requires true;
    ensures distinct(almap_keys(almap_entries(es, fk), fk)) == true;
{
    almap_entries_helper_distinct(es, fk, nil);
}



@*/