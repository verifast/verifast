//@ #include "listex2.gh"

/*@

    //TODO: move general lemma's to list.h or listex.h 
    
lemma void mem_append<t>(t v, list<t> vs1, list<t> vs2) 
    requires true; 
    ensures mem(v, append(vs1, vs2)) == (mem(v, vs1) || mem(v, vs2));
{
    switch(vs1) {
        case nil:
        case cons(h, t): mem_append(v, t, vs2);
    }
}
lemma void mem_snoc<t>(t v1, list<t> vs, t v2) 
    requires true;
    ensures mem(v1, snoc(vs, v2)) == (mem(v1, vs) || v1 == v2);
{
    mem_append(v1, vs, cons(v2, nil));
}


lemma void distinct_snoc<t>(list<t> l, t v)
    requires distinct(l) == true &*& !mem(v, l);
    ensures distinct(snoc(l, v)) == true;
{
    switch(l) {
        case nil:
        case cons(h, t):
           mem_snoc(h, t, v);
           distinct_snoc(t, v);
    }
}

lemma void nth_tail<t>(int i, list<t> l) 
  requires i > 0;
  ensures nth(i-1, tail(l)) == nth(i,l);
{
    switch (l) {
      case nil: 
      case cons(x0, xs0): 
    }
}
  
lemma void length_tail<t>(list<t> l) 
  requires length(l) > 0;
  ensures length(tail(l)) == length (l) - 1;
{
    switch (l) {
      case nil: 
      case cons(x0, xs0): 
    }
}

lemma void nth_snoc_length<t>(list<t> l, t el)
    requires true;
    ensures nth(length(l), snoc(l, el)) == el;
{
    switch (l) {
      case nil: 
      case cons(x0, xs0): 
        nth_snoc_length(xs0, el);
    }
}

lemma void remove_all2_mem<t>(t v, t v2, list<t> l)
    requires true;
    ensures mem(v, remove_all2(v2, l)) == (v != v2 && mem(v, l));
{
    switch(l) {
        case nil:
        case cons(h, t): remove_all2_mem(v, v2, t);
    }
}
lemma void remove_all2_id<t>(t v, list<t> l)
    requires !mem(v, l);
    ensures remove_all2(v, l) == l;
{
    switch(l) {
        case nil:
        case cons(h, t): remove_all2_id(v, t);
    }
}










lemma void append_cons_r_snoc_l<t>(list<t> s1, t v, list<t> s2)
    requires true;
    ensures append(s1, cons(v, s2)) == append(snoc(s1, v), s2);
{
    switch(s1) {
        case nil:
        case cons(h, t): append_cons_r_snoc_l(t, v, s2);
    }
}    





lemma void mem_map_true<ta, tb>(fixpoint (ta, tb) f, list<ta> l, tb b)
    requires mem(b, map(f, l)) == true;
    ensures exwitness<ta>(?a) &*& mem(a, l) == true &*& f(a) == b;
{
    switch(l) {
        case nil:
        case cons(h, t): 
            if(f(h) == b) {
                close exwitness(h);
            } else {
                mem_map_true(f, t, b);
            }
    }
}
lemma void mem_map_false<ta, tb>(fixpoint (ta, tb) f, list<ta> l, ta a, tb b)
    requires mem(b, map(f, l)) == false &*& mem(a, l) == true;
    ensures f(a) != b;
{
    switch(l) {
        case nil:
        case cons(h, t): 
            if(a!=h) mem_map_false(f, t, a, b);
    }
}

lemma void foreach_split<t>(list<t> xs, list<t> ys)
    requires foreach(append(xs, ys), ?p);
    ensures foreach(xs, p) &*& foreach(ys, p);
{
    switch(xs) {
        case nil:
            close foreach(xs, p);
        case cons(x, xs0):
            open foreach(append(xs, ys), p); 
            foreach_split(xs0, ys);
            close foreach(xs, p);
    }
}    

lemma void distinct_insert<t>(list<t> xs, list<t> ys, t z)
    requires distinct(append(xs, ys)) == true &*& !mem(z, append(xs, ys));
    ensures distinct(append(xs, cons(z, ys))) == true;
{
    switch(xs) {
        case nil:
        case cons(x, xs0):
            assert x != z;
            mem_append(x, xs0, ys);
            mem_append(x, xs0, cons(z, ys));
            assert !mem(x, append(xs0, cons(z, ys)));
            distinct_insert(xs0, ys, z);
    }

}

lemma void remove_append<t>(t z, list<t> xs, list<t> ys)
    requires true;
    ensures remove(z, append(xs, ys)) == (mem(z, xs) ? append(remove(z, xs), ys) : append(xs, remove(z, ys)));
{
    switch(xs) {
        case nil:
        case cons(x, xs0):
            if(x != z) remove_append(z, xs0, ys);
    }
}

lemma void insert_distinct_mem<t>(list<t> xs, list<t> ys, t z)
    requires distinct(append(xs, cons(z, ys))) == true;
    ensures !mem(z, xs) &*& !mem(z, ys);
{
    switch(xs) {
        case nil:
        case cons(x, xs0):
            mem_append(x, xs0, cons(z, ys));
            insert_distinct_mem(xs0, ys, z);
    }
}    

lemma void remove_nomem<t>(t el, t el2, list<t> l)
    requires !mem(el, l);
    ensures !mem(el, remove(el2, l));
{
    switch(l) {
        case nil:
        case cons(x, l0):
            remove_nomem(el, el2, l0);
    }
}

lemma void take_append<t>(int k, list<t> l1, list<t> l2)
    requires k >= 0;
    ensures take(k, append(l1, l2)) == (k <= length(l1) ? take(k, l1) : append(l1, take(k-length(l1), l2)));
{
    switch(l1) {
        case nil:
        case cons(h, t):
            if(k != 0) take_append(k-1, t, l2);

    }

}

lemma void drop_append<t>(int k, list<t> l1, list<t> l2)
    requires k >= 0;
    ensures drop(k, append(l1, l2)) == (k <= length(l1) ? append(drop(k, l1), l2) : drop(k-length(l1), l2));
{
    switch(l1) {
        case nil:
        case cons(h, t):
            if(k != 0) drop_append(k-1, t, l2);

    }
}

lemma void split_distinct_unique<t>(list<t>l1, list<t>l2, list<t>l3, list<t>l4, t el)
    requires distinct(append(l1, cons(el, l2))) == true &*& append(l1, cons(el, l2)) == append(l3, cons(el, l4)); 
    ensures l1 == l3 &*& l2 == l4;
{
    switch(l1) {
        case nil:
            switch(l3) {
               case nil:
               case cons(h3, t3):
                   mem_append(el, t3, cons(el, l4));
                   assert false;
            } 
        case cons(h, t):
            switch(l3) {
                case nil:
                   mem_append(el, t, cons(el, l2));
                   assert false;
                case cons(h3, t3):
                split_distinct_unique(t, l2, t3, l4, el);
            }
    }
}

lemma void distinct_snoc_full<t>(list<t> l, t v)
    requires true;
    ensures distinct(snoc(l, v)) == (distinct(l) && !mem(v, l));
{
    switch(l) {
        case nil:
        case cons(h,t):
            mem_snoc(h, t, v);
            distinct_snoc_full(t, v);
    }
}


lemma void distinct_insert_full<t>(list<t> l1, t v, list<t> l2)
    requires true;
    ensures distinct(append(l1, cons(v, l2))) == (distinct(append(l1, l2)) && !mem(v, l1) && !mem(v, l2));
{
    switch(l1) {
        case nil:
        case cons(h,t):
            mem_append(h, t, cons(v, l2));
            mem_append(h, t, l2);
            distinct_insert_full(t, v, l2);
    }
}
    
lemma void distinct_append_comm<t>(list<t> l1, list<t> l2)
    requires true;
    ensures distinct(append(l1, l2)) == distinct(append(l2, l1));
{
    switch(l1) {
        case nil:
            append_nil(l2);
        case cons(l1h, l1t):
            distinct_insert_full(l2, l1h, l1t);
            mem_append(l1h, l1t, l2);
            distinct_append_comm(l1t, l2);
    }
}





lemma void occ_positive<t>(list<t> s, t v)
    requires true; 
    ensures occ(s, v) >= 0;
{
    switch(s) {
        case nil:
        case cons(h, s2):
            occ_positive(s2, v);
    }
}
     
lemma void occ_mem<t>(list<t> l, t v)
    requires !mem(v, l);
    ensures occ(l, v) == 0;
{
    switch(l) {
        case nil: 
        case cons(l1h, l1t):
            occ_mem(l1t, v);
    }
}

lemma void occ_mem_full<t>(list<t> l, t v)
    requires true;
    ensures mem(v, l) == (occ(l, v) > 0);
{
    switch(l) {
        case nil: 
        case cons(l1h, l1t):
            occ_positive(l1t, v);
            occ_mem_full(l1t, v);
    }
}    
lemma void occ_append<t>(list<t>l1, list<t>l2, t v)
    requires true;
    ensures occ(append(l1, l2), v) == occ(l1, v) + occ(l2, v);
{
    switch(l1) {
        case nil: 
        case cons(l1h, l1t):
            occ_append(l1t, l2, v);
    }
}

lemma void pforeach_remove<t>(t x, list<t> xs)
    requires pforeach(xs, ?p) &*& mem(x, xs) == true;
    ensures pforeach(remove(x, xs), p) &*& p(x, _);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            open pforeach(xs, p);
            if(x != x0) {
                pforeach_remove(x, xs0); 
                close pforeach(remove(x, xs), p);
            } else {
            }
    };
}
lemma void pforeach_unremove<t>(t x, list<t> xs)
    requires pforeach(remove(x, xs), ?p) &*& mem(x, xs) == true &*& p(x, _);
    ensures pforeach(xs, p);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if(x != x0) {
                open pforeach(remove(x, xs), p);
                pforeach_unremove(x, xs0); 
            } else {
                assert remove(x, xs) == xs0;
            }
            close pforeach(xs, p);
    };
}
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



lemma void flatten_append<t>(list<list<t> > l1, list<list<t> > l2)
    requires true;
    ensures flatten(append(l1, l2)) == append(flatten(l1), flatten(l2));
{
    switch(l1) {
        case nil: 
        case cons(h, t): 
             flatten_append(t, l2);
             append_assoc(h, flatten(t), flatten(l2));
    }
}
@*/
