//@ #include "dkalmap.gh"

/*@


lemma void dkalmap_get_entry_key<te,tk>(list<te> es, fixpoint(te, tk) fk, tk k)
    requires isDkalmap(es, fk) == true &*& almap_contains_key(es, fk, k) == true;
    ensures fk(almap_get_entry(es, fk, k)) == k;
{
    almap_get_entry_key(es, fk, k);
}

lemma void dkalmap_remove_key_contains_key<te,tk>(list<te> es, fixpoint(te, tk) fk, tk k, tk k2)
    requires isDkalmap(es, fk) == true; 
    ensures almap_contains_key(dkalmap_remove_key(es, fk, k), fk, k2) == (k != k2 && almap_contains_key(es, fk, k2)); 
{
    switch(es) {
        case nil:
        case cons(e, es2):
            dkalmap_remove_key_contains_key(es2, fk, k, k2);
    }
}

lemma void dkalmap_keys_contains_key<te,tk>(list<te> es, fixpoint(te, tk) fk, tk k)
    requires true;
    ensures lset_contains(dkalmap_keys(es, fk), k) == almap_contains_key(es, fk, k);
{
    almap_keys_contains_key(es, fk, k);
}
lemma void dkalmap_restrict_contains_key<te,tk>(list<te> es, list<tk> ks, fixpoint(te, tk) fk, tk k)
    requires isDkalmap(es, fk) == true; 
    ensures almap_contains_key(dkalmap_restrict(es, ks, fk), fk, k) == (lset_contains(ks, k) && almap_contains_key(es, fk, k));
{
    almap_restrict_contains_key(es, ks, fk, k);
}

lemma void dkalmap_remove_key_isDkalmap<te,tk>(list<te> es, fixpoint(te, tk) fk, tk k)
    requires isDkalmap(es, fk) == true; 
    ensures isDkalmap(dkalmap_remove_key(es, fk, k), fk) == true; 
{
    switch(es) {
        case nil:
        case cons(e, es2):
            if(fk(e) != k) {
                dkalmap_remove_key_isDkalmap(es2, fk, k);
                dkalmap_remove_key_contains_key(es2, fk, k, fk(e));
            }
    } 
}

lemma void dkalmap_restrict_isDkalmap<te,tk>(list<te> es, list<tk> ks, fixpoint(te, tk) fk)
    requires isDkalmap(es, fk) == true; 
    ensures isDkalmap(dkalmap_restrict(es, ks, fk), fk) == true;
{
    switch(es) {
        case nil:
        case cons(h, t):
            dkalmap_restrict_isDkalmap(t, ks, fk);
            dkalmap_restrict_contains_key(t, ks, fk, fk(h));
    }
}

lemma void dkalmap_override_contains_key<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk, tk k)
    requires isDkalmap(es1, fk) == true &*& isDkalmap(es2, fk) == true; 
    ensures almap_contains_key(dkalmap_override(es1, es2, fk), fk, k) == (almap_contains_key(es1, fk, k) || almap_contains_key(es2, fk, k));
{
    switch(es1) {
        case nil: 
        case cons(h, t):
            dkalmap_remove_key_isDkalmap(es2, fk, fk(h));
            dkalmap_remove_key_contains_key(es2, fk, fk(h), k);
            dkalmap_override_contains_key(t, dkalmap_remove_key(es2, fk, fk(h)), fk, k);
    }
}

lemma void dkalmap_override_isDkalmap<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk)
    requires isDkalmap(es1, fk) == true &*& isDkalmap(es2, fk) == true; 
    ensures isDkalmap(dkalmap_override(es1, es2, fk), fk) == true;
{
    switch(es1) {
        case nil:
        case cons(h, t):
            dkalmap_remove_key_isDkalmap(es2, fk, fk(h));
            dkalmap_override_isDkalmap(t, dkalmap_remove_key(es2, fk, fk(h)), fk);
            dkalmap_remove_key_contains_key(es2, fk, fk(h), fk(h));
            dkalmap_override_contains_key(t, dkalmap_remove_key(es2, fk, fk(h)), fk, fk(h));
    }
}

// meaning of isDkalmap in terms of its set of keys

lemma void isDkalmap_distinct_keys<te,tk>(list<te> es, fixpoint(te, tk) fk)
    requires true;
    ensures isDkalmap(es, fk) == distinct(dkalmap_keys(es, fk));
{
    switch(es) {
        case nil:
        case cons(e, es2): 
            isDkalmap_distinct_keys(es2, fk);
            dkalmap_keys_contains_key(es2, fk, fk(e));            
    }
}


//lemma's for derived inspectors
lemma void dkalmap_contains_entry_spec<te,tk>(list<te> es, fixpoint(te, tk) fk, te e)
    requires isDkalmap(es, fk) == true;
    ensures dkalmap_contains_entry(es, fk, e) == (almap_contains_key(es, fk, fk(e)) && almap_get_entry(es, fk, fk(e)) == e);
{
    switch(es) {
        case nil:
        case cons(e2, es2): 
            dkalmap_contains_entry_spec(es2, fk, e);
    }
}

lemma void dkalmap_get_value_spec<te,tk,tv>(list<te> es, fixpoint(te, tk) fk, fixpoint(te, tv) fv, tk k)
    requires isDkalmap(es, fk) == true;
    ensures dkalmap_get_value(es, fk, fv, k) == fv(almap_get_entry(es, fk, k));
{
}

lemma void dkalmap_contains_value_true<te,tk,tv>(list<te> es, fixpoint(te, tk) fk, fixpoint(te, tv) fv, tv v)
    requires isDkalmap(es, fk) == true &*& dkalmap_contains_value(es, fk, fv, v) == true;
    ensures exwitness(?e) &*& dkalmap_contains_entry(es, fk, e) == true &*& fv(e) == v;
{
    switch(es) {
        case nil:
        case cons(e, es2):
            if(fv(e)==v) {
                close exwitness(e);
            } else {
                dkalmap_contains_value_true(es2, fk, fv, v);
            }
    }
}

lemma void dkalmap_contains_value_false<te,tk,tv>(list<te> es, fixpoint(te, tk) fk, fixpoint(te, tv) fv, tv v, te e)
    requires isDkalmap(es, fk) == true &*& dkalmap_contains_value(es, fk, fv, v) == false &*& dkalmap_contains_entry(es, fk, e) == true;
    ensures fv(e) != v;
{
    switch(es) {
        case nil:
        case cons(e2, es2):
            if(e != e2) {
                dkalmap_contains_value_false(es2, fk, fv, v, e);
            }
    }
}


lemma void dkalmap_entries_contains_entry<te,tk>(list<te> es, fixpoint(te, tk) fk, te e)
    requires true;
    ensures lset_contains(dkalmap_entries(es, fk), e) == dkalmap_contains_entry(es, fk, e);
{
}

lemma void dkalmap_values_contains_value<te,tk,tv>(list<te> es, fixpoint(te, tk) fk, fixpoint(te, tv) fv, tv v)
    requires true;
    ensures lset_contains(dkalmap_values(es, fk, fv), v) == dkalmap_contains_value(es, fk, fv, v);
{
    switch(es) {
        case nil:
        case cons(e, es2): dkalmap_values_contains_value(es2, fk, fv, v);
    }
}

lemma void dkalmap_disjoint_true<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk, tk k)
    requires dkalmap_disjoint(es1, es2, fk) == true;
    ensures !almap_contains_key(es1, fk, k) || !almap_contains_key(es2, fk, k);
{
    almap_disjoint_true(es1, es2, fk, k);
}

lemma void dkalmap_disjoint_false<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk)
    requires dkalmap_disjoint(es1, es2, fk) == false;
    ensures exwitness(?k) &*& almap_contains_key(es1, fk, k) == true &*& almap_contains_key(es2, fk, k) == true;
{
    almap_disjoint_false(es1, es2, fk);
}

// ctors

lemma void dkalmap_empty_contains_key<te,tk>(list<te> es, fixpoint(te, tk) fk, tk k)
    requires true; 
    ensures !almap_contains_key(dkalmap_empty(), fk, k);  
{
}


lemma void dkalmap_put_contains_key<te,tk>(list<te> es, fixpoint(te, tk) fk, te e, tk k)
    requires isDkalmap(es, fk) == true; 
    ensures almap_contains_key(dkalmap_put(es, fk, e), fk, k) == (fk(e) == k || almap_contains_key(es, fk, k)); 
{
    dkalmap_remove_key_contains_key(es, fk, fk(e), k);
}

lemma void dkalmap_empty_contains_entry<te,tk>(list<te> es, fixpoint(te, tk) fk, te e)
    requires true; 
    ensures !dkalmap_contains_entry(dkalmap_empty(), fk, e);  
{
}

lemma void dkalmap_remove_key_contains_entry<te,tk>(list<te> es, fixpoint(te, tk) fk, tk k, te e)
    requires isDkalmap(es, fk) == true; 
    ensures dkalmap_contains_entry(dkalmap_remove_key(es, fk, k), fk, e) == (k != fk(e) && dkalmap_contains_entry(es, fk, e)); 
{
    switch(es) {
        case nil:
        case cons(e2, es2):
            if(fk(e) == k && fk(e2) == k) {
                dkalmap_contains_entry_spec(es2, fk, e);
            } else {
                dkalmap_remove_key_contains_entry(es2, fk, k, e);
            }
    }
}

lemma void dkalmap_put_contains_entry<te,tk>(list<te> es, fixpoint(te, tk) fk, te e1, te e2)
    requires isDkalmap(es, fk) == true; 
    ensures dkalmap_contains_entry(dkalmap_put(es, fk, e1), fk, e2) == (fk(e1) == fk(e2) ? e1 == e2 : dkalmap_contains_entry(es, fk, e2)); 
{
    dkalmap_remove_key_contains_entry(es, fk, fk(e1), e2);
}

lemma void dkalmap_normalize_equals<te,tk>(list<te> es, fixpoint(te, tk) fk)
    requires true;
    ensures almap_equals(dkalmap_normalize(es, fk), es, fk) == true;
{
    assert dkalmap_normalize(es, fk) == almap_entries(es, fk);
    if(!almap_equals(almap_entries(es, fk), es, fk)) {
        almap_equals_contains_entry_conv(almap_entries(es, fk), es, fk);
        open exwitness(?el);
        almap_entries_contains_entry(es, fk, el);
        almap_entries_distinct(es, fk);
        isDkalmap_distinct_keys(almap_entries(es, fk), fk);
        dkalmap_contains_entry_spec(almap_entries(es, fk), fk, el);
        assert false; 
    }
}

lemma void dkalmap_restrict_contains_entry<te,tk>(list<te> es, list<tk> ks, fixpoint(te, tk) fk, te e)
    requires isDkalmap(es, fk) == true; 
    ensures dkalmap_contains_entry(dkalmap_restrict(es, ks, fk), fk, e) == (lset_contains(ks, fk(e)) && dkalmap_contains_entry(es, fk, e));
{
    almap_restrict_contains_entry(es, ks, fk, e);
    dkalmap_restrict_isDkalmap(es, ks, fk);
    dkalmap_contains_entry_spec(dkalmap_restrict(es, ks, fk), fk, e);
    dkalmap_contains_entry_spec(es, fk, e);
}

lemma void dkalmap_override_contains_entry<te,tk>(list<te> es1, list<te> es2, fixpoint(te, tk) fk, te e)
    requires isDkalmap(es1, fk) == true &*& isDkalmap(es2, fk) == true; 
    ensures dkalmap_contains_entry(dkalmap_override(es1, es2, fk), fk, e) == (almap_contains_key(es1, fk, fk(e)) ? dkalmap_contains_entry(es1, fk, e) : dkalmap_contains_entry(es2, fk, e));
{
    switch(es1) {
        case nil: 
        case cons(h, t):
            assert dkalmap_override(es1, es2, fk) == cons(h, dkalmap_override(t, dkalmap_remove_key(es2, fk, fk(h)), fk));
            dkalmap_remove_key_contains_key(es2, fk, fk(h), fk(h));
            dkalmap_remove_key_contains_entry(es2, fk, fk(h), e);
            dkalmap_remove_key_isDkalmap(es2, fk, fk(h));
            dkalmap_override_contains_entry(t, dkalmap_remove_key(es2, fk, fk(h)), fk, e);
            dkalmap_override_isDkalmap(es1, es2, fk);            
            if(fk(e) == fk(h)) {
                dkalmap_contains_entry_spec(es1, fk, e);
            }
    }
}




//operations maintains isDkalmap
lemma void dkalmap_empty_isDkalmap<te,tk>(list<te> es, fixpoint(te, tk) fk)
    requires true; 
    ensures isDkalmap(dkalmap_empty(), fk) == true;  
{
}


lemma void dkalmap_put_isDkalmap<te,tk>(list<te> es, fixpoint(te, tk) fk, te e)
    requires isDkalmap(es, fk) == true; 
    ensures isDkalmap(dkalmap_put(es, fk, e), fk) == true; 
{
    dkalmap_remove_key_contains_key(es, fk, fk(e), fk(e));
    dkalmap_remove_key_isDkalmap(es, fk, fk(e));   
}

lemma void dkalmap_normalize_isDkalmap<te,tk>(list<te> es, fixpoint(te, tk) fk)
    requires true;
    ensures isDkalmap(dkalmap_normalize(es, fk), fk) == true;
{
    almap_entries_distinct(es, fk);
    isDkalmap_distinct_keys(almap_entries(es, fk), fk);
}  




@*/