//@ #include "map.gh"

/*@

//TODO: refactor this file
//1. remove map, use list of pairs instead.
//2. current version is not total. Therefore, well-definedness conditions need to be specified.

lemma void map_contains_spec<tk,tv>(map<tk,tv> m, tk k, tv v)
    requires true;
    ensures map_contains(m, k, v) == (map_contains_key(m, k) && map_get(m, k) == v);
{
    switch(m) {
        case mnil: 
        case mcons(k2, v2, t): map_contains_spec(t, k, v);
    }
}
lemma void map_contains_functional<tk,tv>(map<tk,tv> m, tk k1, tv v1, tk k2, tv v2)
    requires map_contains(m, k1, v1) && map_contains(m, k2, v2);
    ensures (k1 == k2 ? v1 == v2 : true);
{
    map_contains_spec(m, k1, v1);
    map_contains_spec(m, k2, v2);
}

lemma void map_put_maintains_map_contains<tk,tv>(map<tk,tv> m, tk k1, tv v1, tk k2, tv v2)
    requires k1 != k2;
    ensures map_contains(map_put(m, k2, v2), k1, v1) == map_contains(m, k1, v1);
{
    switch(m) {
        case mnil: 
        case mcons(k3, v3, t): 
            if(k1 != k3 && k2 != k3) {
                map_put_maintains_map_contains(t, k1, v1, k2, v2);
            }
    }
}
lemma void map_put_causes_map_contains<tk,tv>(map<tk,tv> m, tk k1, tv v1)
    requires true;
    ensures map_contains(map_put(m, k1, v1), k1, v1) == true;
{
    switch(m) {
        case mnil: 
        case mcons(k3, v3, t): 
            if(k1 != k3) {
                map_put_causes_map_contains(t, k1, v1);
            }
    }
}
lemma void map_remove_maintains_map_contains<tk,tv>(map<tk,tv> m, tk k1, tv v1, tk k2)
    requires k1 != k2;
    ensures map_contains(map_remove(m, k2), k1, v1) == map_contains(m, k1, v1);
{
    switch(m) {
        case mnil: 
        case mcons(k3, v3, t): 
            if(k1 != k3) {
                map_remove_maintains_map_contains(t, k1, v1, k2);
            }
    }
}


lemma void map_put_invariant<tk,tv>(map<tk,tv> m, tk k1, tk k2, tv v2)
    requires k1 != k2;
    ensures map_get(map_put(m, k2, v2), k1) == map_get(m, k1);
{
    switch(m) {
        case mnil: 
        case mcons(k3, v3, t): 
            if(k1 != k3 && k2 != k3) {
                map_put_invariant(t, k1, k2, v2);
            }
    }
}
lemma void map_remove_invariant<tk,tv>(map<tk,tv> m, tk k1, tk k2)
    requires k1 != k2;
    ensures map_get(map_remove(m, k2), k1) == map_get(m, k1);
{
    switch(m) {
        case mnil: 
        case mcons(k3, v3, t): 
            if(k3 != k1) {
                map_remove_invariant(t, k1, k2);
            }
    }
}
lemma void map_contains_key_after_put<tk,tv>(map<tk,tv> m, tk k1, tk k2, tv v2)
    requires k1 != k2;
    ensures map_contains_key(map_put(m, k2, v2), k1) == map_contains_key(m, k1);
{
    switch(m) {
        case mnil: 
        case mcons(k3, v3, t): 
            if(k1 != k3 && k2 != k3) {
                map_contains_key_after_put(t, k1, k2, v2);
            }
    }
}
lemma void map_contains_key_after_remove<tk,tv>(map<tk,tv> m, tk k1, tk k2)
    requires k1 != k2;
    ensures map_contains_key(map_remove(m, k2), k1) == map_contains_key(m, k1);
{
    switch(m) {
        case mnil: 
        case mcons(k3, v3, t): 
            if(k1 != k3) {
                map_contains_key_after_remove(t, k1, k2);
            }
    }
}

lemma void map_contains_key_mem_map_keys<tk,tv>(map<tk,tv> m, tk k)
    requires true;
    ensures mem(k, map_keys(m)) == map_contains_key(m, k);
{
    switch(m) {
        case mnil: 
        case mcons(k2, v2, t): 
            map_contains_key_mem_map_keys(t, k);
    }
}
lemma void map_put_map_keys<tk,tv>(map<tk,tv> m, tk k, tv v)
    requires !map_contains_key(m, k);
    ensures map_keys(map_put(m, k, v)) == snoc(map_keys(m), k);
{
    switch(m) {
        case mnil: 
        case mcons(k2, v2, t): 
            map_put_map_keys(t, k, v);
    }
}
lemma void map_put_map_values<tk,tv>(map<tk,tv> m, tk k, tv v)
    requires !map_contains_key(m, k);
    ensures map_values(map_put(m, k, v)) == snoc(map_values(m), v);
{
    switch(m) {
        case mnil: 
        case mcons(k2, v2, t): 
            map_put_map_values(t, k, v);
    }
}





lemma void map_put_map_contains_key<tk,tv>(map<tk,tv> m, tk k, tv v)
    requires true;
    ensures map_contains_key(map_put(m, k, v), k) == true;
{
    switch(m) {
        case mnil: 
        case mcons(k2, v2, t): 
            map_put_map_contains_key(t, k, v);
    }    
}

lemma void map_put_map_get<tk,tv>(map<tk,tv> m, tk k, tv v)
    requires true;
    ensures map_get(map_put(m, k, v), k) == v;
{
    switch(m) {
        case mnil: 
        case mcons(k2, v2, t): 
            map_put_map_get(t, k, v);
    }    
}

lemma void map_remove_map_keys<tk,tv>(map<tk,tv> m, tk k)
    requires true;
    ensures map_keys(map_remove(m, k)) == remove(k, map_keys(m));
{
    switch(m) {
        case mnil: 
        case mcons(k2, v2, t): 
            map_remove_map_keys(t, k);
    }
}
lemma void map_disjoint_mnil<tk,tv>(map<tk,tv> m)
    requires true;
    ensures map_disjoint(m, mnil) == true;
{
    switch(m) {
        case mnil:
        case mcons(k, v, t): 
            map_disjoint_mnil(t);
    }
}
lemma void map_alldisjoint_mnil<tk,tv>(list<map<tk,tv> > ms)
    requires true;
    ensures map_alldisjoint(mnil, ms) == true;
{
    switch(ms) {
        case nil:
        case cons(h, t): 
            map_alldisjoint_mnil(t);
    }
}
lemma void map_disjoint_cons_r<tk,tv>(map<tk,tv> m1, tk k, tv v, map<tk,tv> m2)
    requires true;
    ensures map_disjoint(m1, mcons(k, v, m2)) == (!map_contains_key(m1, k) && map_disjoint(m1, m2));
{
    switch(m1) {
        case mnil: map_disjoint_mnil(m2);
        case mcons(k2,v2,t):
            map_disjoint_cons_r(t, k, v, m2);
    }
}
lemma void map_disjoint_sym<tk,tv>(map<tk,tv> m1, map<tk,tv> m2)
    requires true;
    ensures map_disjoint(m1, m2) == map_disjoint(m2, m1);
{
    switch(m1) {
        case mnil: map_disjoint_mnil(m2);
        case mcons(k,v,t):
            map_disjoint_sym(t, m2);
            map_disjoint_cons_r(m2, k, v, t);
    }
}

lemma void map_alldisjoint_snoc<tk,tv>(map<tk,tv> m, list<map<tk,tv> > ms, map<tk,tv> m2)
    requires true;
    ensures map_alldisjoint(m, snoc(ms, m2)) == (map_alldisjoint(m, ms) && map_disjoint(m, m2));
{
    switch(ms) {
        case nil: 
        case cons(h, t): 
            map_alldisjoint_snoc(m, t, m2);
    }
}

lemma void maps_disjoint_snoc<tk,tv>(list<map<tk,tv> > ms, map<tk,tv> m)
    requires true;
    ensures maps_disjoint(snoc(ms, m)) == (maps_disjoint(ms) && map_alldisjoint(m, ms));
{
    switch(ms) {
        case nil: 
        case cons(h, t): 
            map_alldisjoint_snoc(h, t, m);
            maps_disjoint_snoc(t, m);
            map_disjoint_sym(m, h);
    }
}

lemma void maps_disjunion_snoc_mnil<tk,tv>(list<map<tk,tv> > ms)
    requires true;
    ensures maps_disjunion(snoc(ms, mnil)) == maps_disjunion(ms);
{
    switch(ms) {
        case nil: 
        case cons(h, t): 
            maps_disjunion_snoc_mnil(t);
    }
}

@*/
