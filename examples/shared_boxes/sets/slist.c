//@ #include "slist.gh"
/*@


lemma void sorted_mem_cons(int v, int x, list<int> l)
    requires sorted(cons(x, l)) == true &*& v < x;
    ensures !mem(v, cons(x, l)); 
{
    switch(l) {
        case nil:
        case cons(lh,lt):
            sorted_mem_cons(v, lh, lt);
    }
}
lemma void sorted_mem_cons2(int v, int x, int y, list<int> l)
    requires sorted(cons(x, cons(y, l))) == true &*& x < v &*& v <= y;
    ensures mem(v, cons(x, cons(y, l))) == (v == y); 
{
    if(v != y) {
        sorted_mem_cons(v, y, l);
    }
}
lemma void sorted_cons(int x, list<int> l)
    requires sorted(cons(x, l)) == true;
    ensures sorted(l) == true;
{
    switch(l) {
        case nil:
        case cons(lh, lt):
            sorted_cons(lh, lt);
    }
}
lemma void sorted_append(int x, list<int> l1, int y, list<int> l2)
    requires sorted(append(cons(x, l1), cons(y, l2))) == true;
    ensures x < y; 
{
    switch(l1) {
        case nil:
        case cons(l1h, l1t):
            sorted_append(l1h, l1t, y, l2);
    }
}

lemma void sorted_mem_append(int v, list<int> l1, int x, list<int> l2)
    requires sorted(append(l1, cons(x, l2))) == true &*& x < v;
    ensures mem(v, append(l1, cons(x, l2))) == mem(v, l2); 
{
    switch(l1) {
        case nil:
        case cons(l1h, l1t):
            sorted_append(l1h, l1t, x, l2);
            sorted_cons(l1h, append(l1t, cons(x, l2)));
            sorted_mem_append(v, l1t, x, l2);
    }
}
lemma void sorted_append_split(list<int> l1, list<int> l2)
    requires sorted(append(l1, l2)) == true;
    ensures sorted(l2) == true;
{
    switch(l1) {
        case nil:
        case cons(lh, lt):
            sorted_cons(lh, append(lt, l2));
            sorted_append_split(lt, l2);
    }
}
lemma void sorted_append_split2(list<int> l1, list<int> l2)
    requires sorted(append(l1, l2)) == true;
    ensures sorted(l1) == true;
{
    switch(l1) {
        case nil:
        case cons(lh, lt):
            switch(lt) {
                case nil:
                case cons(h, t):
            }
            sorted_cons(lh, append(lt, l2));
            sorted_append_split2(lt, l2);
    }
}
lemma void sorted_snoc(list<int> l, int v)
    requires sorted(snoc(l, v)) == true;
    ensures sorted(l) == true;
{
    sorted_append_split2(l, cons(v, nil));
}

lemma void sorted_insert_mem(int v, list<int> vs) 
    requires true;
    ensures mem(v, sorted_insert(v, vs)) == true;
{
    switch(vs) {
        case nil:
        case cons(h, t):
            if(h!=v) {
                sorted_insert_mem(v, t);
            }
    }
}

lemma void append_snoc<t>(list<t> l1, t val, list<t> l2) 
    requires true;
    ensures append(snoc(l1, val), l2) == append(l1, cons(val, l2));
{
    switch(l1) {
        case nil:
        case cons(lh, lt):
            append_snoc(lt, val, l2);
    }
    
}

lemma void sorted_insert_sorted(int v, list<int> vs)
    requires sorted(vs) == true;
    ensures sorted(sorted_insert(v, vs)) == true;
{
    switch(vs) {
        case nil:
        case cons(h, t):
            if(h<v) {
                sorted_cons(h, t);
                sorted_insert_sorted(v, t);
                switch(t) {
                    case nil:
                    case cons(h2, t2):
                }
            } 
    }
}

lemma void si_append(int v, list<int> l1, int l2h, list<int>l2t)
    requires sorted(append(l1, cons(l2h, l2t))) == true &*& v < l2h;
    ensures sorted_insert(v, append(l1, cons(l2h, l2t))) == append(sorted_insert(v, l1), cons(l2h, l2t));
{
    switch(l1) {
        case nil:
        case cons(l1h, l1t):
            sorted_cons(l1h, append(l1t, cons(l2h, l2t)));
            si_append(v, l1t, l2h, l2t);
    }
}

lemma void si1(int v, list<int> l)
    requires sorted(cons(INT_MIN, snoc(l, INT_MAX))) == true &*& v > INT_MIN &*& v < INT_MAX;
    ensures sorted_insert(v, cons(INT_MIN, snoc(l, INT_MAX))) == cons(INT_MIN, snoc(sorted_insert(v, l), INT_MAX));
{
    assert sorted_insert(v, cons(INT_MIN, snoc(l, INT_MAX))) == cons(INT_MIN, sorted_insert(v, snoc(l, INT_MAX)));
    sorted_cons(INT_MIN, snoc(l, INT_MAX));
    si_append(v, l, INT_MAX, nil);
    assert sorted_insert(v, snoc(l, INT_MAX)) == snoc(sorted_insert(v, l), INT_MAX);
    
}
lemma void si2(int v, list<int> l1, int pv, int cv, list<int> l2)
    requires sorted(append(l1, cons(pv, cons(cv, l2)))) == true &*& pv < v &*& v < cv;
    ensures sorted_insert(v, append(l1, cons(pv, cons(cv, l2)))) == append(l1, cons(pv, cons(v, cons(cv, l2))));
{
    switch(l1) {
        case nil:
        case cons(h, t): 
            sorted_append(h, t, pv, cons(cv, l2));
            sorted_cons(h, append(t, cons(pv, cons(cv, l2))));
            si2(v, t, pv, cv, l2);
    }
}

lemma void si3(int v, list<int> l1, int pv, int cv, list<int> l2)
    requires sorted(append(l1, cons(pv, cons(cv, l2)))) == true &*& v == cv;
    ensures sorted_insert(v, append(l1, cons(pv, cons(cv, l2)))) == append(l1, cons(pv, cons(cv, l2)));
{
    switch(l1) {
        case nil:
        case cons(h, t): 
            sorted_append(h, t, pv, cons(cv, l2));
            sorted_append_split(l1, cons(pv, cons(cv, l2)));
            sorted_cons(h, append(t, cons(pv, cons(cv, l2))));
            si3(v, t, pv, cv, l2);
    }
}

lemma void append_nonnil<t>(list<t> l1, list<t> l2)
    requires l2 != nil;
    ensures append(l1, l2) != nil;
{
    switch(l1) {
        case nil:
        case cons(h, t): append_nonnil(t, l2);
    }
}     
    
lemma void last_append<t>(list<t> l1, list<t> l2) 
    requires l2 != nil;
    ensures last(append(l1, l2)) == last(l2);
{
    switch(l1) {
        case nil:
        case cons(h, t): append_nonnil(t, l2); last_append(t, l2); 
    }
} 
lemma void last_snoc<t>(list<t> l, t v) 
    requires true;
    ensures last(snoc(l, v)) == v;
{
    last_append(l, cons(v, nil)); 
}
     
lemma void last_eq(list<int> vs, list<int> vs1, int pv, int cv)
    requires cons(INT_MIN, snoc(vs, INT_MAX)) == append(vs1, cons(pv, cons(cv, nil)));
    ensures cv == INT_MAX;
{
    last_snoc(vs, INT_MAX);
    last_append(vs1, cons(pv, cons(cv, nil)));
}

lemma void remove_sorted(int v, list<int> vs)
    requires sorted(vs) == true;
    ensures sorted(remove(v, vs)) == true;
{
    switch(vs) {
        case nil:
        case cons(h, t): 
            sorted_cons(h, t);
            if(h != v) {
                remove_sorted(v, t);
                switch(t) {
                    case nil:
                    case cons(h2, t2):
                        if(h2 == v) {
                            switch(t2) {
                                case nil:
                                case cons(h3, t3):
                            }
                        } 
                }
            }
    }
}
    
lemma void remove_nomem<t>(t v,  list<t> l)
    requires !mem(v, l);
    ensures remove(v, l) == l;
{
    switch(l) {
        case nil:
        case cons(h, t):
            remove_nomem(v, t);
    }
}
lemma void remove_append<t>(t v, list<t> l1, list<t> l2)
    requires !mem(v, l2);
    ensures remove(v, append(l1, l2)) == append(remove(v, l1), l2);
{
    switch(l1) {
        case nil:
            remove_nomem(v, l2);
        case cons(h, t):
            remove_nomem(v, l2);
            if(v != h) {
                assert remove(v, append(l1, l2)) == cons(h, remove(v, append(t, l2)));
                remove_append(v, t, l2);
            } 
    }
}
    
lemma void remove_helper1(int v, list<int> l)
    requires sorted(cons(INT_MIN, snoc(l, INT_MAX))) == true &*& v > INT_MIN &*& v < INT_MAX;
    ensures remove(v, cons(INT_MIN, snoc(l, INT_MAX))) == cons(INT_MIN, snoc(remove(v, l), INT_MAX));
{
    remove_append(v, l, cons(INT_MAX, nil));
}

lemma void remove_sorted_nomem(int v, int h, list<int> t)
    requires sorted(cons(h, t)) == true &*& v<h;
    ensures remove(v, cons(h,t)) == cons(h,t);
{
    switch(t) {
        case nil:
        case cons(h2, t2):
            remove_sorted_nomem(v, h2, t2);
    }
}

lemma void remove_helper2(int v, list<int> l1, int pv, int cv, list<int> l2)
    requires sorted(append(l1, cons(pv, cons(cv, l2)))) == true &*& pv < v &*& v < cv;
    ensures remove(v, append(l1, cons(pv, cons(cv, l2)))) == append(l1, cons(pv, cons(cv, l2)));
{
    switch(l1) {
        case nil: 
            remove_sorted_nomem(v, cv, l2);
        case cons(h, t):
            sorted_cons(h, append(t, cons(pv, cons(cv, l2))));
            sorted_append(h, t, pv, cons(cv, l2));
            remove_helper2(v, t, pv, cv, l2);
    }
}
lemma void remove_helper3(int v, list<int> l1, int pv, int cv, list<int> l2)
    requires sorted(append(l1, cons(pv, cons(cv, l2)))) == true &*& v == cv;
    ensures remove(v, append(l1, cons(pv, cons(cv, l2)))) == append(l1, cons(pv, l2));
{
    switch(l1) {
        case nil: 
        case cons(h, t):
            sorted_cons(h, append(t, cons(pv, cons(cv, l2))));
            sorted_append(h, t, pv, cons(cv, l2));
            sorted_append_split(l1, cons(pv, cons(cv, l2)));
            remove_helper3(v, t, pv, cv, l2);
    }
}

lemma void sorted_remove_all2_h(int v, int h, list<int> t) 
    requires sorted(cons(h, t)) == true && h > v;
    ensures remove_all2(v, cons(h, t)) == cons(h, t);
{
    switch(t){
        case nil: 
        case cons(h2, t2): 
            sorted_remove_all2_h(v, h2, t2);
    }
}
lemma void sorted_remove_all2(int v, list<int> l) 
    requires sorted(l) == true;
    ensures remove(v, l) == remove_all2(v, l);
{
    switch(l){
        case nil: 
        case cons(h, t): 
            sorted_cons(h, t);
            sorted_remove_all2(v, t);
            if(h >= v) {
                switch(t) {
                    case nil:
                    case cons(h2, t2): sorted_remove_all2_h(v, h2, t2);
                }
                assert remove_all2(v, t) == t;
            }
    }    
} 

lemma void remove_all2_spec<t>(t v, t v2, list<t> l)
    requires true;
    ensures mem(v2, remove_all2(v, l)) == (mem(v2, l) && v2 != v);
{
    switch(l) {
        case nil:
        case cons(h, t):
            remove_all2_spec(v, v2, t);
    }
}

lemma void replace_append<t>(list<t> la, list<t> lb, t el, list<t> l2)
    requires !mem(el, la);
    ensures replace(append(la, lb), el, l2) == append(la, replace(lb, el, l2));
{
    switch(la) {
       case nil:
       case cons(h, t):
           replace_append(t, lb, el, l2);
    }
}

lemma void sorted_insert_mem_increasing(list<int> l, int v, int v2)
    requires v != v2 &*& sorted(l) == true;
    ensures mem(v2, sorted_insert(v, l)) == mem(v2, l);
{
    switch(l) {
        case nil:
        case cons(h, t):
            sorted_cons(h, t);
            sorted_insert_mem_increasing(t, v, v2);
    }
}

@*/