//@ #include "lmap.gh"

/*@

// lemma's about basic inspectors

lemma void lmap_get_entry_key<tk,tv>(list<pair<tk,tv> > es, tk k)
    requires lmap_contains_key(es, k) == true;
    ensures fst(lmap_get_entry(es, k)) == k;
{
    almap_get_entry_key(es, fst, k);
}

//lemma's for derived inspectors
lemma void lmap_contains_entry_spec<tk,tv>(list<pair<tk,tv> > es, tk k, tv v)
    requires true;
    ensures lmap_contains_entry(es, k, v) == (lmap_contains_key(es, k) && lmap_get_entry(es, k) == pair(k, v));
{
}
    
lemma void lmap_get_value_spec<tk,tv>(list<pair<tk,tv> > es, tk k)
    requires true;
    ensures lmap_get_value(es, k) == snd(lmap_get_entry(es, k));
{
}

lemma void lmap_contains_value_true<tk,tv>(list<pair<tk,tv> > es, tv v)
    requires lmap_contains_value(es, v) == true;
    ensures exwitness(?k) &*& lmap_contains_entry(es, k, v) == true;
{
    almap_contains_value_true(es, fst, snd, v);
    open exwitness<pair<tk, tv> >(?e);
    switch(e) {
        case pair(k, v2): 
           assert v == v2;
           close exwitness(k);
        
    }
}

lemma void lmap_contains_value_false<tk,tv>(list<pair<tk,tv> > es, tv v, tk k, tv v2)
    requires lmap_contains_value(es, v) == false &*& lmap_contains_entry(es, k, v2) == true;
    ensures v != v2;
{
    almap_contains_value_false(es, fst, snd, v, pair(k, v2));
}

lemma void lmap_keys_contains_key<tk,tv>(list<pair<tk,tv> > es, tk k)
    requires true;
    ensures lset_contains(lmap_keys(es), k) == lmap_contains_key(es, k);
{
    almap_keys_contains_key(es, fst, k);
}

lemma void lmap_entries_contains_entry<tk,tv>(list<pair<tk,tv> > es, tk k, tv v)
    requires true;
    ensures lset_contains(lmap_entries(es), pair(k, v)) == lmap_contains_entry(es, k, v);
{
    almap_entries_contains_entry(es, fst, pair(k, v));
}

lemma void lmap_values_contains_value<tk,tv>(list<pair<tk,tv> > es, tv v)
    requires true;
    ensures lset_contains(lmap_values(es), v) == lmap_contains_value(es, v);
{
}

lemma void lmap_disjoint_true<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2, tk k)
    requires lmap_disjoint(es1, es2) == true;
    ensures !lmap_contains_key(es1, k) || !lmap_contains_key(es2, k);
{
    almap_disjoint_true(es1, es2, fst, k);
}

lemma void lmap_disjoint_false<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2)
    requires lmap_disjoint(es1, es2) == false;
    ensures exwitness(?k) &*& lmap_contains_key(es1, k) == true &*& lmap_contains_key(es2, k) == true;
{
    almap_disjoint_false(es1, es2, fst);
}

// specification of construtors

lemma void lmap_empty_contains_key<tk,tv>(list<pair<tk,tv> > es, tk k)
    requires true; 
    ensures !lmap_contains_key(lmap_empty(), k);  
{
}

lemma void lmap_remove_key_contains_key<tk,tv>(list<pair<tk,tv> > es, tk k, tk k2)
    requires true; 
    ensures lmap_contains_key(lmap_remove_key(es, k), k2) == (k != k2 && lmap_contains_key(es, k2)); 
{
    almap_remove_key_contains_key(es, fst, k, k2);
}

lemma void lmap_put_contains_key<tk,tv>(list<pair<tk,tv> > es, tk k2, tv v, tk k)
    requires true; 
    ensures lmap_contains_key(lmap_put(es, k2, v), k) == (k2 == k || lmap_contains_key(es, k)); 
{
    almap_put_contains_key(es, fst, pair(k2, v), k);
}

lemma void lmap_empty_contains_entry<tk,tv>(list<pair<tk,tv> > es, tk k, tv v)
    requires true; 
    ensures !lmap_contains_entry(lmap_empty(), k, v);  
{
}

lemma void lmap_remove_key_contains_entry<tk,tv>(list<pair<tk,tv> > es, tk k, tk k2, tv v)
    requires true; 
    ensures lmap_contains_entry(lmap_remove_key(es, k), k2, v) == (k != k2 && lmap_contains_entry(es, k2, v)); 
{
    almap_remove_key_contains_entry(es, fst, k, pair(k2, v));
}

lemma void lmap_put_contains_entry<tk,tv>(list<pair<tk,tv> > es, tk k1, tv v1, tk k2, tv v2)
    requires true; 
    ensures lmap_contains_entry(lmap_put(es, k1, v1), k2, v2) == (k1 == k2 ? v1 == v2 : lmap_contains_entry(es, k2, v2)); 
{
}

lemma void lmap_override_contains_entry<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2, tk k, tv v)
    requires true; 
    ensures lmap_contains_entry(lmap_override(es1, es2), k, v) == (lmap_contains_key(es1, k) ? lmap_contains_entry(es1, k, v) : lmap_contains_entry(es2, k, v));
{
    almap_override_contains_entry(es1, es2, fst, pair(k, v));
}

lemma void lmap_restrict_contains_entry<tk,tv>(list<pair<tk,tv> > es, list<tk> ks, tk k, tv v)
    requires true; 
    ensures lmap_contains_entry(lmap_restrict(es, ks), k, v) == (lset_contains(ks, k) && lmap_contains_entry(es, k, v));
{
    almap_restrict_contains_entry(es, ks, fst, pair(k, v));
}

lemma void lmap_override_contains_key<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2, tk k)
    requires true; 
    ensures lmap_contains_key(lmap_override(es1, es2), k) == (lmap_contains_key(es1, k) || lmap_contains_key(es2, k));
{
    almap_override_contains_key(es1, es2, fst, k);
}

lemma void lmap_restrict_contains_key<tk,tv>(list<pair<tk,tv> > es, list<tk> ks, tk k)
    requires true; 
    ensures lmap_contains_key(lmap_restrict(es, ks), k) == (lset_contains(ks, k) && lmap_contains_key(es, k));
{
    almap_restrict_contains_key(es, ks, fst, k);
}




// specification of almap_submap and almap_equals

lemma void lmap_submap_contains_entry<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2, tk k, tv v)
    requires lmap_submap(es1, es2) == true;
    ensures lmap_contains_entry(es1, k, v) ? lmap_contains_entry(es2, k, v) == true : true;
{
    almap_submap_contains_entry(es1, es2, fst, pair(k, v));
}

lemma void lmap_equals_contains_entry<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2, tk k, tv v)
    requires lmap_equals(es1, es2) == true;
    ensures lmap_contains_entry(es1, k, v) == lmap_contains_entry(es2, k, v);
{
    almap_equals_contains_entry(es1, es2, fst, pair(k, v));
}

lemma void lmap_submap_contains_key<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2, tk k)
    requires lmap_submap(es1, es2) == true;
    ensures lmap_contains_key(es1, k) ? lmap_contains_key(es2, k) == true : true;
{
    almap_submap_contains_key(es1, es2, fst, k);
}

lemma void lmap_equals_contains_key<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2, tk k)
    requires lmap_equals(es1, es2) == true;
    ensures lmap_contains_key(es1, k) == lmap_contains_key(es2, k);
{
    almap_equals_contains_key(es1, es2, fst, k);
}

lemma void lmap_submap_contains_entry_conv<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2)
    requires lmap_submap(es1, es2) == false;
    ensures exwitness2(?k, ?v) &*& lmap_contains_entry(es1, k, v) == true &*& !lmap_contains_entry(es2, k, v);
{
    almap_submap_contains_entry_conv(es1, es2, fst);
    open exwitness<pair<tk,tv> >(?e);
    switch(e) {
        case pair(k, v): close exwitness2(k, v);
    }
}

lemma void lmap_equals_contains_entry_conv<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2)
    requires lmap_equals(es1, es2) == false;
    ensures exwitness2(?k, ?v) &*& lmap_contains_entry(es1, k, v) != lmap_contains_entry(es2, k, v);
{
    almap_equals_contains_entry_conv(es1, es2, fst);
    open exwitness<pair<tk,tv> >(?e);
    switch(e) {
        case pair(k, v): close exwitness2(k, v);
    }
}

//misc
lemma void lmap_entries_distinct<tk,tv>(list<pair<tk,tv> > es)
    requires true;
    ensures distinct(lmap_keys(lmap_entries(es))) == true;
{
    almap_entries_distinct(es, fst);
}

@*/