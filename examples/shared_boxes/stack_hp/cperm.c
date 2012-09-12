//@ #include "cperm.gh"
//@ #include "ghost_cells.gh"
//@ #include "raw_ghost_lists.gh" 
//@ #include "listex.gh"
/*@

fixpoint real sum(list<real> l) {
    switch(l) {
        case nil: return 0;
        case cons(h,t): return h+sum(t); 
    } 
}
lemma void sum_append(list<real> l1, list<real> l2)
    requires true;
    ensures sum(append(l1,l2)) == sum(l1) + sum(l2);
{
    switch(l1) {
        case nil:
        case cons(h, t): sum_append(t, l2);
    }
}

fixpoint real sumSnd<t>(list<pair<t, real> > l){ return sum(map(snd, l)); }

predicate gres2<t1,t2>(t1 v1, t2 v2) = true;

lemma void list_split<t>(list<t> l, t v)
    requires mem(v, l) == true;
    ensures gres2(?l1, ?l2) &*& l == append(l1, cons(v, l2)) &*& mem(v, l1) == false;
{
    switch(l) {
        case nil:
        case cons(h, l2):
            if(h == v) {
                close gres2(nil, l2);
            } else {
                list_split(l2, v);
                open gres2(?l2a, ?l2b);
                close gres2(cons(h, l2a), l2b);
            }
    }
}
lemma void remove_helper<t>(list<t>l1, list<t>l2, t v)
    requires mem(v, l1) == false;
    ensures remove(v, append(l1, cons(v, l2))) == append(l1, l2);
{
    switch(l1) {
        case nil:
        case cons(h, l12): remove_helper(l12, l2, v);
    }
}

predicate pforeach<t>(list<t> xs, predicate(t;) p;) =
    switch (xs) {
        case nil: return true;
        case cons(x, xs0): return p(x) &*& pforeach(xs0, p);
    };

lemma void pforeach_split<t>(list<t> xs, list<t> ys)
    requires pforeach(append(xs, ys), ?p);
    ensures pforeach(xs, p) &*& pforeach(ys, p);
{
    switch(xs) {
        case nil:
        case cons(x, xs2): 
            open pforeach(append(xs, ys), p);
            pforeach_split(xs2, ys);
            close pforeach(xs, p);
    } 
}
lemma void pforeach_append<t>(list<t> xs, list<t> ys)
    requires pforeach(xs, ?p) &*& pforeach(ys, p);
    ensures pforeach(append(xs, ys), p);
{
    switch(xs) {
        case nil:
        case cons(x, xs2): 
            open pforeach(xs, p);
            pforeach_append(xs2, ys);
            close pforeach(append(xs, ys), p);
    } 
}

lemma void pforeach_remove<t>(t x, list<t> xs)
    requires pforeach(xs, ?p) &*& mem(x, xs) == true;
    ensures pforeach(remove(x, xs), p) &*& p(x);
{
    list_split(xs, x);
    open gres2(?xs1, ?xs2);
    remove_helper(xs1, xs2, x);
    pforeach_split(xs1, cons(x, xs2));
    open pforeach(cons(x, xs2), p);
    pforeach_append(xs1, xs2);
}
lemma void pforeach_unremove<t>(t x, list<t> xs)
    requires pforeach(remove(x, xs), ?p) &*& mem(x, xs) == true &*& p(x);
    ensures pforeach(xs, p);
{
    list_split(xs, x);
    open gres2(?xs1, ?xs2);
    remove_helper(xs1, xs2, x);
    pforeach_split(xs1, xs2);
    close pforeach(cons(x, xs2), p);
    pforeach_append(xs1, cons(x, xs2));
}


predicate fracsInv(pair<int, real> p;) = snd(p) > 0 &*& snd(p) < 1;

lemma void fracsInv_helper(list<pair<int, real> > l)
    requires pforeach(l, fracsInv);
    ensures pforeach(l, fracsInv) &*& sumSnd(l) >= 0;
{
    switch(l) {
        case nil:
        case cons(h, t):
            open pforeach(l, fracsInv);
            open fracsInv(h);
            fracsInv_helper(t);
            close fracsInv(h);
            close pforeach(l, fracsInv);
    }
}

predicate cptInternal<ta,tb>(int id, predicate(ta; tb) pred; ta a, tb b, int count, real rem) =
    [_]ghost_cell<pair<int,int> >(id, ?fids)  &*&
    ghost_cell<ta>(fst(fids), a) &*&
    raw_ghost_list<real>(snd(fids), ?c, ?fracs) &*& 
    rem == 1 - sumSnd(fracs) &*&
    count == length(fracs) &*&
    pforeach(fracs, fracsInv) &*&
    rem > 0 &*& rem <= 1 &*&
    [rem]pred(a, b);

predicate cptracker<ta,tb>(int id, predicate(ta; tb) p; ta a, int count, tb b) =
    cptInternal(id, p, a, b, count, ?rem);

predicate cptracker_precursor<ta,tb>(int id, predicate(ta; tb) p; ta a) = 
    [_]ghost_cell<pair<int,int> >(id, ?fids)  &*&
    ghost_cell<ta>(fst(fids), a) &*&
    raw_ghost_list<real>(snd(fids), 0, nil) &*&
    pforeach(nil, fracsInv);


predicate cpticket(int id, int tid; real frac) = 
    [_]ghost_cell<pair<int,int> >(id, ?fids) &*&
    ghost_cell<int>(tid, ?k) &*&
    raw_ghost_list_member_handle(snd(fids), k, frac) &*&
    frac > 0 &*& frac < 1;

        

lemma int create_cptracker_precursor<ta,tb>(predicate(ta; tb) p, ta a)
    requires true;
    ensures cptracker_precursor<ta,tb>(result, p, a);
{
    int fracsId = create_raw_ghost_list();
    int argsId = create_ghost_cell(a);
    int id = create_ghost_cell(pair(argsId, fracsId));
    leak ghost_cell(id, pair(argsId, fracsId));
    close pforeach(nil, fracsInv);
    close cptracker_precursor<ta,tb>(id, p, a);
    return id;
}
lemma void convert_cptracker_precursor<ta,tb>(int id)
    requires cptracker_precursor<ta,tb>(id, ?p, ?a) &*& p(a, ?b);
    ensures cptracker<ta,tb>(id, p, a, 0, b);
{
    open cptracker_precursor<ta,tb>(id, p, a);
    close cptInternal(id, p, a, b, 0, 1);
    close cptracker(id, p, a, 0, b);    
}
lemma int create_cpticket<ta,tb>(int id)
    requires cptracker<ta,tb>(id, ?p, ?a, ?count, ?b);
    ensures cptracker<ta,tb>(id, p, a, count+1, b) &*& cpticket(id, result, ?f) &*& [f]p(a, b) &*& 0 < f;
{
    open cptracker(id, p, a, count, b);
    open cptInternal(id, p, a, b, count, ?rem);
    real result = rem / 3;
    assert [_]ghost_cell<pair<int,int> >(id, ?info);
    int fid = snd(info);
    assert raw_ghost_list(fid, ?n, ?fracs);
    raw_ghost_list_add(fid, result);
    map_append(snd, fracs, cons(pair(n, result), nil));
    sum_append(map(snd, fracs), cons(result, nil));
    int tid = create_ghost_cell(n);
    close cpticket(id, tid, result);
    //natlength_append(fracs, cons(pair(n, result), nil));
    //nat_sum_comm(natlength(fracs), succ(zero));
    close pforeach(cons(pair(n, result), nil), fracsInv);
    pforeach_append(fracs, cons(pair(n, result), nil));
    close cptInternal(id, p, a, b, count+1, rem-result);
    close cptracker(id, p, a, count+1, b);
    return tid;
}


    
lemma void destroy_cpticket<ta,tb>(int id, int tid)
    requires cptracker<ta,tb>(id, ?p, ?a, ?count, ?b) &*& cpticket(id, tid, ?f) &*& [f]p(a, ?b2) &*& 0 < f;
    ensures cptracker<ta,tb>(id, p, a, count - 1, b) &*& count > 0 &*& b == b2;
{
    open cptracker(id, p, a, count, b);
    open cptInternal(id, p, a, b, count, ?rem);
    open cpticket(id, tid, f);
    assert [_]ghost_cell<pair<int,int> >(id, ?info);
    assert [1/2]ghost_cell<int>(tid, ?k);
    int fid = snd(info);
    assert raw_ghost_list(fid, ?c, ?fracs) &*& raw_ghost_list_member_handle(fid, k, f);
    raw_ghost_list_match(fid, k);
    assert mem(pair(k, f), fracs) == true;
    list_split(fracs, pair(k,f));
    open gres2(?fr1, ?fr2);
    assert rem == 1 - sumSnd(append(fr1, cons(pair(k, f), fr2)));
    map_append(snd, fr1, cons(pair(k, f), fr2));
    sum_append(map(snd, fr1), cons(f, map(snd, fr2)));
    assert rem == 1 - (sumSnd(fr1) + f + sumSnd(fr2));
    raw_ghost_list_remove(fid, k);
    assert raw_ghost_list(fid, ?c2, remove(pair(k, f), fracs));
    remove_helper(fr1, fr2, pair(k, f));
    map_append(snd, fr1, fr2);
    sum_append(map(snd, fr1), map(snd, fr2));
    assert sumSnd(remove(pair(k, f), fracs)) == sumSnd(fr1) + sumSnd(fr2);
    pforeach_remove(pair(k, f), fracs);
    open fracsInv(pair(k, f));
    pforeach_split(fr1, fr2);
    fracsInv_helper(fr1);
    fracsInv_helper(fr2);
    pforeach_append(fr1, fr2);
    close cptInternal(id, p, a, b, count-1, rem+f);
    close cptracker(id, p, a, count-1, b);
    leak ghost_cell(tid, k);
}
lemma void destroy_cptracker<ta,tb>(int id)
    requires cptracker<ta,tb>(id, ?p, ?a, 0, ?b);
    ensures p(a, b);
{
    open cptracker(id, p, a, 0, b);
    open cptInternal(id, p, a, b, 0, ?rem);
    assert [_]ghost_cell<pair<int,int> >(id, ?info) &*& raw_ghost_list(snd(info), ?c, ?fracs);
    switch(fracs) { case nil: case cons(h, t): assert false; }
    assert rem == 1;
    leak ghost_cell(fst(info), a);
    leak raw_ghost_list(snd(info), c, fracs);
}

lemma void cptracker_match<ta,tb>(int id)
    requires cptracker<ta, tb>(id, ?p, ?a, ?c, ?b) &*& [?f]p(a, ?b2) &*& f > 0;
    ensures cptracker<ta, tb>(id, p, a, c, b) &*& [f]p(a, b2) &*& b == b2;
{
    open cptracker(id, p, a, c, b);
    open cptInternal(id, p, a, b, c, ?rem);
    close cptInternal(id, p, a, b, c, rem);
    close cptracker(id, p, a, c, b);
}

    
lemma int create_cptracker<ta,tb>(predicate(ta; tb) p, ta a)
    requires p(a, ?b);
    ensures cptracker<ta,tb>(result, p, a, 0, b);
{
    int id = create_cptracker_precursor(p, a);
    convert_cptracker_precursor(id);
    return id;
}

@*/
