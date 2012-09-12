//@ #include "dklmap.gh"

/*@

// lemma's about basic inspectors

lemma void dklmap_get_entry_key<tk,tv>(list<pair<tk,tv> > es, tk k)
    requires isDklmap(es) == true &*& lmap_contains_key(es, k) == true;
    ensures fst(lmap_get_entry(es, k)) == k;
{
    dkalmap_get_entry_key(es, fst, k);
}


//lemma's for derived inspectors
lemma void dklmap_contains_entry_spec<tk,tv>(list<pair<tk,tv> > es, tk k, tv v)
    requires isDklmap(es) == true;
    ensures dklmap_contains_entry(es, k, v) == (lmap_contains_key(es, k) && lmap_get_entry(es, k) == pair(k, v));
{
    dkalmap_contains_entry_spec(es, fst, pair(k, v));
}

lemma void dklmap_get_value_spec<tk,tv>(list<pair<tk,tv> > es, tk k)
    requires isDklmap(es) == true;
    ensures dklmap_get_value(es, k) == snd(lmap_get_entry(es, k));
{
}

lemma void dklmap_contains_value_true<tk,tv>(list<pair<tk,tv> > es, tv v)
    requires isDklmap(es) == true &*& dklmap_contains_value(es, v) == true;
    ensures exwitness(?k) &*& dklmap_contains_entry(es, k, v) == true;
{
    dkalmap_contains_value_true(es, fst, snd, v);
    open exwitness<pair<tk,tv> >(?e);
    switch(e) { case pair(k, v2): close exwitness(k); }
}

lemma void dklmap_contains_value_false<tk,tv>(list<pair<tk,tv> > es, tv v, tk k, tv v2)
    requires isDklmap(es) == true &*& dklmap_contains_value(es, v) == false &*& dklmap_contains_entry(es, k, v2) == true;
    ensures v != v2;
{
    dkalmap_contains_value_false(es, fst, snd, v, pair(k, v2));
}

lemma void dklmap_keys_contains_key<tk,tv>(list<pair<tk,tv> > es, tk k)
    requires true;
    ensures lset_contains(dklmap_keys(es), k) == lmap_contains_key(es, k);
{
    dkalmap_keys_contains_key(es, fst, k);
}

lemma void dklmap_entries_contains_entry<tk,tv>(list<pair<tk,tv> > es, tk k, tv v)
    requires true;
    ensures lset_contains(dklmap_entries(es), pair(k, v)) == dklmap_contains_entry(es, k, v);
{
}

lemma void dklmap_values_contains_value<tk,tv>(list<pair<tk,tv> > es, tv v)
    requires true;
    ensures lset_contains(dklmap_values(es), v) == dklmap_contains_value(es, v);
{
    dkalmap_values_contains_value(es, fst, snd, v); 
}

lemma void dklmap_disjoint_true<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2, tk k)
    requires dklmap_disjoint(es1, es2) == true;
    ensures !lmap_contains_key(es1, k) || !lmap_contains_key(es2, k);
{
    dkalmap_disjoint_true(es1, es2, fst, k);
}

lemma void dklmap_disjoint_false<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2)
    requires dklmap_disjoint(es1, es2) == false;
    ensures exwitness(?k) &*& lmap_contains_key(es1, k) == true &*& lmap_contains_key(es2, k) == true;
{
    dkalmap_disjoint_false(es1, es2, fst);
}


// specification ctors wrt lmap_contains_key and almap_contains_entry

lemma void dklmap_empty_contains_key<tk,tv>(list<pair<tk,tv> > es, tk k)
    requires true; 
    ensures !lmap_contains_key(dklmap_empty(), k);  
{
}

lemma void dklmap_remove_key_contains_key<tk,tv>(list<pair<tk,tv> > es, tk k, tk k2)
    requires isDklmap(es) == true; 
    ensures lmap_contains_key(dklmap_remove_key(es, k), k2) == (k != k2 && lmap_contains_key(es, k2)); 
{
    dkalmap_remove_key_contains_key(es, fst, k, k2);
}

lemma void dklmap_put_contains_key<tk,tv>(list<pair<tk,tv> > es, tk k, tv v, tk k2)
    requires isDklmap(es) == true; 
    ensures lmap_contains_key(dklmap_put(es, k, v), k2) == (k == k2 || lmap_contains_key(es, k2)); 
{
    dkalmap_put_contains_key(es, fst, pair(k,v), k2);
}

lemma void dklmap_empty_contains_entry<tk,tv>(list<pair<tk,tv> > es, tk k, tv v)
    requires true; 
    ensures !dklmap_contains_entry(dklmap_empty(), k, v);  
{
}

lemma void dklmap_remove_key_contains_entry<tk,tv>(list<pair<tk,tv> > es, tk k, tk k2, tv v)
    requires isDklmap(es) == true; 
    ensures dklmap_contains_entry(dklmap_remove_key(es, k), k2, v) == (k != k2 && dklmap_contains_entry(es, k2, v)); 
{
    dkalmap_remove_key_contains_entry(es, fst, k, pair(k2, v));
}

lemma void dklmap_put_contains_entry<tk,tv>(list<pair<tk,tv> > es, tk k1, tv v1, tk k2, tv v2)
    requires isDklmap(es) == true; 
    ensures dklmap_contains_entry(dklmap_put(es, k1, v1), k2, v2) == (k1 == k2 ? v1 == v2 : dklmap_contains_entry(es, k2, v2)); 
{
    dkalmap_put_contains_entry(es, fst, pair(k1, v1), pair(k2, v2));
}

lemma void dklmap_normalize_equals<tk,tv>(list<pair<tk,tv> > es)
    requires true;
    ensures lmap_equals(dklmap_normalize(es), es) == true;
{
    dkalmap_normalize_equals(es, fst);
}

lemma void dklmap_override_contains_entry<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2, tk k, tv v)
    requires isDklmap(es1) == true &*& isDklmap(es2) == true; 
    ensures dklmap_contains_entry(dklmap_override(es1, es2), k, v) == (lmap_contains_key(es1, k) ? dklmap_contains_entry(es1, k, v) : dklmap_contains_entry(es2, k, v));
{
    dkalmap_override_contains_entry(es1, es2, fst, pair(k, v));
}

lemma void dklmap_restrict_contains_entry<tk,tv>(list<pair<tk,tv> > es, list<tk> ks, tk k, tv v)
    requires isDklmap(es) == true; 
    ensures dklmap_contains_entry(dklmap_restrict(es, ks), k, v) == (lset_contains(ks, k) && dklmap_contains_entry(es, k, v));
{
    dkalmap_restrict_contains_entry(es, ks, fst, pair(k, v));
}

lemma void dklmap_override_contains_key<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2, tk k)
    requires isDklmap(es1) == true &*& isDklmap(es2) == true; 
    ensures lmap_contains_key(dklmap_override(es1, es2), k) == (lmap_contains_key(es1, k) || lmap_contains_key(es2, k));
{
    dkalmap_override_contains_key(es1, es2, fst, k);
}

lemma void dklmap_restrict_contains_key<tk,tv>(list<pair<tk,tv> > es, list<tk> ks, tk k)
    requires isDklmap(es) == true; 
    ensures lmap_contains_key(dklmap_restrict(es, ks), k) == (lset_contains(ks, k) && lmap_contains_key(es, k));
{
    dkalmap_restrict_contains_key(es, ks, fst, k);
}

//meaning of isDklmap
lemma void isDklmap_distinct_keys<tk,tv>(list<pair<tk,tv> > es)
    requires true;
    ensures isDklmap(es) == distinct(dklmap_keys(es));
{
    isDkalmap_distinct_keys(es, fst);
}


//operations maintain isDklmap
lemma void dklmap_empty_isDklmap<tk,tv>(list<pair<tk,tv> > es)
    requires true; 
    ensures isDklmap(dklmap_empty()) == true;  
{
}

lemma void dklmap_remove_key_isDklmap<tk,tv>(list<pair<tk,tv> > es, tk k)
    requires isDklmap(es) == true; 
    ensures isDklmap(dklmap_remove_key(es, k)) == true; 
{
    dkalmap_remove_key_isDkalmap(es, fst, k);
}

lemma void dklmap_put_isDklmap<tk,tv>(list<pair<tk,tv> > es, tk k, tv v)
    requires isDklmap(es) == true; 
    ensures isDklmap(dklmap_put(es, k, v)) == true; 
{
    dkalmap_put_isDkalmap(es, fst, pair(k, v));
}

lemma void dklmap_normalize_isDklmap<tk,tv>(list<pair<tk,tv> > es)
    requires true;
    ensures isDklmap(dklmap_normalize(es)) == true;
{
    dkalmap_normalize_isDkalmap(es, fst);
}

lemma void dklmap_override_isDklmap<tk,tv>(list<pair<tk,tv> > es1, list<pair<tk,tv> > es2)
    requires isDklmap(es1) == true &*& isDklmap(es2) == true; 
    ensures isDklmap(dklmap_override(es1, es2)) == true;
{
    dkalmap_override_isDkalmap(es1, es2, fst);
}

lemma void dklmap_restrict_isDklmap<tk,tv>(list<pair<tk,tv> > es, list<tk> ks)
    requires isDklmap(es) == true; 
    ensures isDklmap(dklmap_restrict(es, ks)) == true;
{
    dkalmap_restrict_isDkalmap(es, ks, fst);
}

@*/