//@ #include "fraction_store.gh"
//@ #include "raw_ghost_lists.gh"
//@ #include "ghost_cells.gh"
//@ #include "listex2.gh"

/*@

fixpoint real sumSnd(list<pair<int, real> > l) {
    switch(l) {
        case nil: return 0;
        case cons(h,t): return snd(h) + sumSnd(t);
    }
}

predicate helper(list<pair<int, real> > l; real rem) =
    switch(l) {
        case nil: return rem == 0;
        case cons(h, t): return snd(h) > 0 &*& helper(t, ?rem0) &*& rem == snd(h) + rem0;
    };

lemma void helper_rem_positive(list<pair<int, real> > l) 
    requires helper(l, ?rem);
    ensures helper(l, rem) &*& rem >= 0;
{
    switch(l) {
        case nil:
            open helper(l, rem);
            close helper(l, rem);
        case cons(h, t):
            open helper(l, rem);
            helper_rem_positive(t);
            close helper(l, rem);
    }
}

predicate gres2<t1,t2>(t1 v1, t2 v2) = true;

lemma void helper_split(list<pair<int, real> > l, pair<int, real> p)
    requires helper(l, ?rem) &*& mem(p, l) == true;
    ensures gres2(?l1, ?l2) &*& helper(l1, ?rem1) &*& helper(l2, ?rem2) &*& l == append(l1, cons(p, l2)) &*& rem == rem1 + snd(p) + rem2 &*& snd(p) > 0 &*& !mem(p, l1);
{
    switch(l) {
        case nil:
            open helper(l, rem);
            assert false;
        case cons(h, t):
            open helper(l, rem);
            if(h == p) {
                close helper(nil, 0);
                close gres2(nil, t);
            } else {
                helper_split(t, p);
                open gres2(?t1, ?t2);
                close helper(cons(h, t1), _);
                close gres2(cons(h, t1), t2);
            }
    }
  
}

lemma void helper_join(list<pair<int, real> > l1, list<pair<int, real> > l2)
    requires helper(l1, ?rem1) &*& helper(l2, ?rem2); 
    ensures helper(append(l1, l2), ?rem) &*& rem == rem1 + rem2;
{
    switch(l1) {
        case nil:
            open helper(l1, rem1);
          
        case cons(h, t):
            open helper(l1, rem1);
            helper_join(t, l2);
            close helper(append(l1, l2), _);
    }
}


predicate fraction_store<ta,tb>(int id, predicate(ta; tb) p; ta a, int count, real rem)=
    [_]ghost_cell<pair<ta, int> >(id, ?info) &*&
    a == fst(info) &*&
    raw_ghost_list(snd(info), _, ?l) &*&
    count == length(l) &*&
    helper(l, rem) &*&
    rem > 0 ? [rem] p(a, _) : true;

predicate fraction_store_precursor<ta, tb>(int id, predicate(ta; tb) p)=
    ghost_cell<pair<ta, int> >(id, _); 


predicate fraction_store_ticket<ta, tb>(int id, real f)=
    [_]ghost_cell<pair<ta, int> >(id, ?info) &*&
    raw_ghost_list_member_handle(snd(info), ?tid, f);


lemma int create_fraction_store<ta, tb>(predicate(ta; tb) p, ta a)
    requires true;
    ensures fraction_store<ta,tb>(result, p, a, 0, 0);
{
    int rglist = create_raw_ghost_list<real>();
    int res = create_ghost_cell(pair(a, rglist));
    leak ghost_cell<pair<ta, int> >(res, pair(a, rglist));
    close fraction_store(res, p, a, 0, 0);
    return res;
}
    
lemma void fraction_store_deposit<ta, tb>(int id, real f)
    requires fraction_store<ta,tb>(id, ?p, ?a, ?c, ?r) &*& [f]p(a, _) &*& 0 < f;
    ensures fraction_store<ta,tb>(id, p, a, c + 1, r + f) &*& fraction_store_ticket<ta, tb>(id, f) &*& r >= 0;
{
    open fraction_store(id, p, a, c, r);
    assert [_]ghost_cell<pair<ta,int> >(id, ?info) &*& raw_ghost_list(snd(info), ?k, ?l);
    helper_rem_positive(l);
    raw_ghost_list_add(snd(info), f);
    close helper(nil, 0);
    close helper(cons(pair(k, f), nil), f);
    helper_join(l, cons(pair(k, f), nil));
    close fraction_store(id, p, a, c + 1, r + f);
    close fraction_store_ticket(id, f);
}    
    
lemma void fraction_store_withdraw<ta, tb>(int id, real f)
    requires fraction_store<ta,tb>(id, ?p, ?a, ?c, ?r) &*& fraction_store_ticket<ta, tb>(id, f);
    ensures fraction_store<ta,tb>(id, p, a, c - 1, r - f) &*& [f]p(a, _) &*& 0 < f &*& f <= r &*& c > 0;
{
    open fraction_store(id, p, a, c, r);
    assert [_]ghost_cell<pair<ta,int> >(id, ?info) &*& raw_ghost_list(snd(info), ?k, ?l);
    open fraction_store_ticket(id, f);
    assert raw_ghost_list_member_handle<real>(snd(info), ?n, f);
    raw_ghost_list_match(snd(info), n);
    raw_ghost_list_remove(snd(info), n);
    helper_rem_positive(l);
    helper_split(l, pair(n, f)); 
    open gres2(?l1, ?l2);
    helper_rem_positive(l1);
    helper_rem_positive(l2);
    helper_join(l1, l2);
    remove_append(pair(n, f), l1, cons(pair(n, f), l2));
    close fraction_store(id, p, a, c - 1, r - f);
}

lemma void fraction_store_dispose<ta, tb>(int id)
    requires fraction_store<ta,tb>(id, ?p, ?a, 0, _);
    ensures true;
{
    open fraction_store(id, p, a, 0, _);
    assert [_]ghost_cell<pair<ta,int> >(id, ?info) &*& raw_ghost_list(snd(info), ?k, ?l);
    switch(l) {
        case cons(h, t):
            open helper(cons(h, t), 0); 
            helper_rem_positive(t);
            assert false;
        case nil:
    }
    open helper(nil, _);
    leak raw_ghost_list(snd(info), k, l);
}

lemma void fraction_store_info<ta, tb>(int id)
    requires fraction_store<ta,tb>(id, ?p, ?a, ?c, ?r);
    ensures fraction_store<ta,tb>(id, p, a, c, r) &*& 0 <= r &*& c >= 0;
{
    open fraction_store(id, p, a, c, r);
    assert [_]ghost_cell<pair<ta,int> >(id, ?info) &*& raw_ghost_list(snd(info), ?k, ?l);
    helper_rem_positive(l);
    close fraction_store(id, p, a, c, r);
}

lemma void fraction_store_ticket_info<ta, tb>(int id, real f)
    requires fraction_store<ta,tb>(id, ?p, ?a, ?c, ?r) &*& fraction_store_ticket<ta, tb>(id, f);
    ensures fraction_store<ta,tb>(id, p, a, c, r) &*& fraction_store_ticket<ta, tb>(id, f) &*& 0 < f &*& f <= r &*& c > 0;
{
    open fraction_store(id, p, a, c, r);
    assert [_]ghost_cell<pair<ta,int> >(id, ?info) &*& raw_ghost_list(snd(info), ?k, ?l);
    open fraction_store_ticket(id, f);
    assert raw_ghost_list_member_handle<real>(snd(info), ?n, f);
    raw_ghost_list_match(snd(info), n);
    helper_rem_positive(l);
    helper_split(l, pair(n, f)); 
    open gres2(?l1, ?l2);
    helper_rem_positive(l1);
    helper_rem_positive(l2);
    close helper(cons(pair(n, f), l2), _);
    helper_join(l1, cons(pair(n, f), l2));
    close fraction_store_ticket(id, f);
    close fraction_store(id, p, a, c, r);
}

lemma void fraction_store_info_unique<ta, tb>(int id, real f)
    requires fraction_store<ta,tb>(id, ?p, ?a, ?c, ?r) &*& is_predicate_unique(?lem, p) &*& [f]p(a, _) &*& 0 < f;
    ensures fraction_store<ta,tb>(id, p, a, c, r) &*& is_predicate_unique(lem, p) &*& [f]p(a, _) &*& 0 <= r &*& r <= 1 - f;
{
    open fraction_store(id, p, a, c, r);
    assert [_]ghost_cell<pair<ta,int> >(id, ?info) &*& raw_ghost_list(snd(info), ?k, ?l);
    helper_rem_positive(l);
    lem(a);
    close fraction_store(id, p, a, c, r);
}        
lemma void fraction_store_ticket_info_unique<ta, tb>(int id, real f, real f2)
    requires fraction_store<ta,tb>(id, ?p, ?a, ?c, ?r) &*& is_predicate_unique(?lem, p) &*& fraction_store_ticket<ta, tb>(id, f) &*& [f2]p(a, _) &*& 0 < f2;
    ensures fraction_store<ta,tb>(id, p, a, c, r) &*& is_predicate_unique(lem, p) &*& fraction_store_ticket<ta, tb>(id, f) &*& [f2]p(a, _) &*& 0 < f &*& f2 <= 1 - f;
{
    fraction_store_ticket_info(id, f);
    fraction_store_info_unique(id, f2);
}

lemma void fraction_store_unique_empty<ta, tb>(int id)
    requires fraction_store<ta,tb>(id, ?p, ?a, ?c, ?r) &*& is_predicate_unique(?lem, p) &*& p(a, _);
    ensures fraction_store<ta,tb>(id, p, a, c, r) &*& is_predicate_unique(lem, p) &*& p(a, _) &*& c == 0 &*& r == 0;
{
    open fraction_store(id, p, a, c, r);
    assert [_]ghost_cell<pair<ta,int> >(id, ?info) &*& raw_ghost_list(snd(info), ?k, ?l);
    lem(a);
    open helper(l, r);
    switch(l) {
        case cons(h, t):
            helper_rem_positive(t);
            assert false;
        case nil:
    }
    close fraction_store(id, p, a, c, r);
}

lemma int create_fraction_store_precursor<ta, tb>(predicate(ta; tb) p)
    requires true;
    ensures fraction_store_precursor(result, p);
{
    int res = create_ghost_cell(pair(default_value<ta>(), 0));
    close fraction_store_precursor(res, p);
    return res;
}    
lemma void convert_fraction_store_precursor<ta, tb>(int id, predicate(ta; tb) p, ta a)
    requires fraction_store_precursor(id, p);
    ensures fraction_store<ta,tb>(id, p, a, 0, 0);
{
    open fraction_store_precursor(id, p);
    int rglist = create_raw_ghost_list<real>();
    ghost_cell_mutate(id, pair(a, rglist));
    leak ghost_cell<pair<ta, int> >(id, pair(a, rglist));
    close fraction_store(id, p, a, 0, 0);
}
@*/
