//@ #include "set.gh"

// mathematical sets using a list representation 
// lists can be seen as multisets, and all functions ignore the multiplicity of the elements
// therefore, the functions are total: if you modify the lists without the set_* functions, all set_* functions still work

//TODO: rename to listset ?

/*@

lemma void set_empty_mem<t>(t v)
    requires true; 
    ensures !mem(v, set_empty());
{
}

lemma void set_add_mem<t>(list<t> s, t v, t v2)
    requires true; 
    ensures mem(v2, set_add(s, v)) == (v == v2 || mem(v2, s));
{
}

lemma void set_singleton_mem<t>(t v, t v2)
    requires true; 
    ensures mem(v2, set_singleton(v)) == (v == v2);
{
}

lemma void set_remove_mem<t>(list<t> s, t el, t el2)
    requires true;
    ensures mem(el2, set_remove(s, el)) == (el != el2 && mem(el2, s));
{
    switch(s) {
        case nil:
        case cons(h,t):
            set_remove_mem(t, el, el2);
    }
}

lemma void set_union_mem<t>(list<t> s1, list<t> s2, t el)
    requires true;
    ensures mem(el, set_union(s1, s2)) == (mem(el, s1) || mem(el, s2));
{
    switch(s1) {
        case nil:
        case cons(h,t):
            set_union_mem(t, s2, el);
    }
}

lemma void set_inters_mem<t>(list<t> s1, list<t> s2, t el)
    requires true;
    ensures mem(el, set_inters(s1, s2)) == (mem(el, s1) &&mem(el, s2));
{
    switch(s1) {
        case nil:
        case cons(h,t):
            set_inters_mem(t, s2, el);
    }
}

lemma void set_diff_mem<t>(list<t> s1, list<t> s2, t el)
    requires true;
    ensures mem(el, set_diff(s1, s2)) == (mem(el, s1) && !mem(el, s2));
{
    switch(s1) {
        case nil:
        case cons(h,t):
            set_diff_mem(t, s2, el);
    }
}

lemma void set_subset_mem<t>(list<t> s1, list<t> s2, t el)
    requires set_subset(s1, s2) == true;
    ensures mem(el, s1) ? mem(el, s2)==true : true;
{
    switch(s1) {
        case nil:
        case cons(h,t):
            if(h != el) set_subset_mem(t, s2, el);
    }
}

lemma void set_subset_set_add<t>(list<t> s1, t el, list<t> s2)
    requires set_subset(s1, s2) == true;
    ensures set_subset(s1, set_add(s2, el)) == true;
{
    switch(s1) {
        case nil:
        case cons(h,t):
            set_subset_set_add(t, el, s2);
    }    
}

lemma void set_subset_refl<t>(list<t> s)
    requires true;
    ensures set_subset(s, s) == true;
{
    switch(s){
        case nil:
        case cons(h,t):
            set_subset_refl(t);
            set_subset_set_add(t, h, t);
    }
}
lemma void set_equals_refl<t>(list<t> s)
    requires true;
    ensures set_equals(s, s) == true;
{
    set_subset_refl(s);    
}

lemma void set_equals_mem<t>(list<t> s1, list<t> s2, t el)
    requires set_equals(s1, s2) == true;
    ensures mem(el, s1) == mem(el, s2);
{
    set_subset_mem(s1, s2, el);
    set_subset_mem(s2, s1, el);
}
lemma void set_subset_add_both<t>(list<t> s1, list<t> s2, t el)
    requires set_subset(s1, s2) == true;
    ensures set_subset(set_add(s1, el), set_add(s2, el)) == true;
{
    set_subset_set_add(s1, el, s2);
}
lemma void set_equals_add_both<t>(list<t> s1, list<t> s2, t el)
    requires set_equals(s1, s2) == true;
    ensures set_equals(set_add(s1, el), set_add(s2, el)) == true;
{
    set_subset_set_add(s1, el, s2);
    set_subset_set_add(s2, el, s1);
}

lemma void set_equals_symmetric<t>(list<t> s1, list<t> s2)
    requires true;
    ensures set_equals(s1, s2) == set_equals(s2, s1);
{

}

lemma void set_subset_transitive<t>(list<t> s1, list<t> s2, list<t> s3)
    requires set_subset(s1, s2) == true &*& set_subset(s2, s3) == true;
    ensures set_subset(s1, s3) == true;
{
    switch(s1) {
        case nil:
        case cons(s1h, s1t):
            set_subset_mem(s2, s3, s1h);
            set_subset_transitive(s1t, s2, s3);
    }
}

lemma void set_equals_transitive<t>(list<t> s1, list<t> s2, list<t> s3)
    requires set_equals(s1, s2) == true &*& set_equals(s2, s3) == true;
    ensures set_equals(s1, s3) == true;
{
    set_subset_transitive(s1, s2, s3);
    set_subset_transitive(s3, s2, s1);
}

lemma void set_add_assoc_helper<t>(list<t> s, t e1, t e2) 
    requires true;
    ensures set_subset(set_add(set_add(s, e1),e2), set_add(set_add(s, e2),e1)) == true;
{
    set_subset_refl(s);
    set_subset_set_add(s, e2, s);
    set_subset_set_add(s, e1, set_add(s, e2));
}

lemma void set_add_assoc<t>(list<t> s, t e1, t e2) 
    requires true;
    ensures set_equals(set_add(set_add(s, e1),e2), set_add(set_add(s, e2),e1)) == true;
{
    set_add_assoc_helper(s, e1, e2);
    set_add_assoc_helper(s, e2, e1);
}

lemma void set_subset_append_l<t>(list<t> s1, list<t> s2, list<t> s3)
    requires true;
    ensures set_subset(set_union(s1, s2), s3) == (set_subset(s1, s3) && set_subset(s2, s3));
{
    switch(s1) {
        case nil:
        case cons(h,t):
            set_subset_append_l(t, s2, s3);
    }
}
lemma void set_subset_append_r1<t>(list<t> s1, list<t> s2, list<t> s3)
    requires set_subset(s1, s2) == true;
    ensures set_subset(s1, set_union(s2, s3)) == true;
{
    switch(s1) {
        case nil:
        case cons(h,t):
            set_union_mem(s2, s3, h);
            set_subset_append_r1(t, s2, s3);        
    }
}
lemma void set_subset_append_r2<t>(list<t> s1, list<t> s2, list<t> s3)
    requires set_subset(s1, s3) == true;
    ensures set_subset(s1, set_union(s2, s3)) == true;
{
    switch(s1) {
        case nil:
        case cons(h,t):
            set_union_mem(s2, s3, h);
            set_subset_append_r2(t, s2, s3);        
    }
}

lemma void set_subset_cons_snoc<t>(list<t> s1, list<t> s2, t el)
    requires true;
    ensures set_subset(s1, snoc(s2, el)) == set_subset(s1, cons(el, s2));
{
    switch(s1) {
        case nil:
        case cons(h, t):
            mem_snoc(h, s2, el);
            assert mem(h, snoc(s2, el)) == mem(h, cons(el, s2)); 
            set_subset_cons_snoc(t, s2, el);
    }
}

lemma void set_equals_cons_snoc<t>(list<t> s, t el)
    requires true;
    ensures set_equals(cons(el, s), snoc(s, el)) == true;
{
    set_subset_cons_snoc(cons(el, s), s, el);
    set_subset_refl(cons(el, s));
    set_subset_cons_snoc(snoc(s, el), s, el);
    set_subset_refl(snoc(s, el));    
}

lemma void set_equals_empty<t>(list<t> s) 
    requires set_equals(s, set_empty()) == true;
    ensures s == set_empty();
{
    switch(s) {
        case nil: 
        case cons(h, t):
    }   
}

lemma void set_subset_equals_r<t>(list<t> s1, list<t>  s2, list<t> s3)
    requires set_subset(s1, s2) == true &*& set_equals(s2, s3) == true;
    ensures set_subset(s1, s3) == true; 
{
    switch(s1) {
        case nil:
        case cons(h,t):
           set_equals_mem(s2, s3, h);
           set_subset_equals_r(t, s2, s3);
    }
}

lemma void set_remove_not_mem<t>(list<t> s, t el)
    requires !mem(el, s);
    ensures set_remove(s, el) == s;
{
    switch(s) {
        case nil:
        case cons(h,t):
            set_remove_not_mem(t, el);
    }
}


lemma void set_subset_set_remove<t>(list<t> s1, list<t> s2, t el)
    requires set_subset(s1, s2) == true;
    ensures set_subset(set_remove(s1, el), set_remove(s2, el)) == true;
{
    switch(s1) {
        case nil: 
        case cons(h,t):
            set_remove_mem(s2, el, h);
            set_subset_set_remove(t, s2, el);
    }
}

lemma void set_equals_set_remove<t>(list<t> s1, list<t> s2, t el)
    requires set_equals(s1, s2) == true;
    ensures set_equals(set_remove(s1, el), set_remove(s2, el)) == true;
{
    set_subset_set_remove(s1, s2, el);
    set_subset_set_remove(s2, s1, el);
}

lemma void set_subset_remove_r<t>(list<t> s1, list<t> s2, t v) 
    requires !mem(v, s1) &*& set_subset(s1, s2) == true;
    ensures set_subset(s1, set_remove(s2, v)) == true;
{
    set_subset_set_remove(s1, s2, v);
    set_remove_not_mem(s1, v);
}

lemma void set_filter2_union<t, ti>(list<t> s1, list<t> s2, fixpoint(t, ti, bool) f, ti i)
    requires true;
    ensures set_filter2(set_union(s1, s2), f, i) == set_union(set_filter2(s1, f, i), set_filter2(s2, f, i));
{
    switch(s1) {
        case nil:
        case cons(h, t):
            set_filter2_union(t, s2, f, i);
    }
}
lemma void set_filter2_subset<t, ti>(list<t> s, fixpoint(t, ti, bool) f, ti i)
    requires true;
    ensures set_subset(set_filter2(s, f, i), s) == true;
{
    switch(s) {
        case nil:
        case cons(h, t):
            set_filter2_subset(t, f, i);
            set_subset_set_add(set_filter2(t, f, i), h, t);
    }
}

lemma void set_filter2_spec<t,ti>(list<t> s, fixpoint(t, ti, bool) f, ti i, t el) 
    requires true;
    ensures mem(el, set_filter2(s, f, i)) == (f(el, i) && mem(el, s));
{
    switch(s) {
        case nil: 
        case cons(h, t):
            set_filter2_spec(t, f, i, el);
    }
}

//TODO: more lemma's about sets

@*/
