//@ #include "lset.gh"

/*@

//relation between contains and other functions

lemma void lset_empty_contains<t>(t v)
    requires true; 
    ensures !lset_contains(lset_empty(), v);
{
}
lemma void lset_add_contains<t>(list<t> s, t v, t v2)
    requires true; 
    ensures lset_contains(lset_add(s, v), v2) == (v == v2 || lset_contains(s, v2));
{
}

lemma void lset_singleton_contains<t>(t v, t v2)
    requires true; 
    ensures lset_contains(lset_singleton(v), v2) == (v == v2);
{
}

lemma void lset_union_contains<t>(list<t> s1, list<t> s2, t el)
    requires true;
    ensures lset_contains(lset_union(s1, s2), el) == (lset_contains(s1, el) || lset_contains(s2, el));
{
    switch(s1) {
        case nil:
        case cons(h,t):
            lset_union_contains(t, s2, el);
    }
}

lemma void lset_inters_contains<t>(list<t> s1, list<t> s2, t el)
    requires true;
    ensures lset_contains(lset_inters(s1, s2), el) == (lset_contains(s1, el) && lset_contains(s2, el));
{
    switch(s1) {
        case nil:
        case cons(h,t):
            lset_inters_contains(t, s2, el);
    }
}

lemma void lset_diff_contains<t>(list<t> s1, list<t> s2, t el)
    requires true;
    ensures lset_contains(lset_diff(s1, s2), el) == (lset_contains(s1, el) && !lset_contains(s2, el));
{
    switch(s1) {
        case nil:
        case cons(h,t):
            lset_diff_contains(t, s2, el);
    }
}

lemma void lset_remove_contains<t>(list<t> s, t el, t el2)
    requires true;
    ensures lset_contains(lset_remove(s, el), el2) == (el != el2 && lset_contains(s, el2));
{
    switch(s) {
        case nil:
        case cons(h,t):
            lset_remove_contains(t, el, el2);
    }
}


lemma void lset_subset_contains<t>(list<t> s1, list<t> s2, t el)
    requires lset_subset(s1, s2) == true;
    ensures lset_contains(s1, el) ? lset_contains(s2, el)==true : true;
{
    switch(s1) {
        case nil:
        case cons(h,t):
            if(h != el) lset_subset_contains(t, s2, el);
    }
}

lemma void lset_subset_contains_conv<t>(list<t> s1, list<t> s2)
    requires lset_subset(s1, s2) == false;
    ensures exwitness(?el) &*& lset_contains(s1, el) == true &*& !lset_contains(s2, el);
{
    switch(s1) {
        case nil:
        case cons(h,t):
            if(lset_contains(s2, h)) {
                lset_subset_contains_conv(t, s2);
            } else {
                close exwitness(h);
            }
    }
}

lemma void lset_equals_contains<t>(list<t> s1, list<t> s2, t el)
    requires lset_equals(s1, s2) == true;
    ensures lset_contains(s1, el) == lset_contains(s2, el);
{
    lset_subset_contains(s1, s2, el);
    lset_subset_contains(s2, s1, el);
}


lemma void lset_equals_contains_conv<t>(list<t> s1, list<t> s2)
    requires lset_equals(s1, s2) == false;
    ensures exwitness(?el) &*& lset_contains(s1, el) != lset_contains(s2, el);
{
    if(lset_subset(s1, s2)) {
        lset_subset_contains_conv(s2, s1);
    } else {
        lset_subset_contains_conv(s1, s2);
    }
}

/*        
// relation between add and union 

lemma void lset_union_set_add_r<t>(list<t> s1, list<t> s2, t el)
    requires true;
    ensures lset_union(s1, lset_add(s2, el)) == lset_union(lset_union(s1, lset_singleton(el)), s2);
{
    switch(s1) {
        case nil:
        case cons(h, t):
            lset_union_set_add_r(t, s2, el);
    }
}   

//properties wrt empty set

lemma void lset_union_empty_r<t>(list<t> s)
    requires true;
    ensures lset_union(s, nil) == s; 
{
}
    
lemma void lset_union_empty_l<t>(list<t> s)
    requires true;
    ensures lset_union(nil, s) == s; 
{
}

lemma void lset_inters_empty_r<t>(list<t> s)
    requires true;
    ensures lset_inters(s, nil) == nil; 
{
    switch(s) {
        case nil:
        case cons(h, t): lset_inters_empty_r(t);
    }
}
    
lemma void lset_inters_empty_l<t>(list<t> s)
    requires true;
    ensures lset_inters(nil, s) == nil; 
{
}

lemma void lset_diff_empty_r<t>(list<t> s)
    requires true;
    ensures lset_diff(s, nil) == s; 
{
    switch(s) {
        case nil:
        case cons(h, t): lset_diff_empty_r(t);
    }
}
    
lemma void lset_diff_empty_l<t>(list<t> s)
    requires true;
    ensures lset_diff(nil, s) == nil; 
{

}

//properties of subset

lemma void lset_subset_empty_l<t>(list<t> s)
    requires true;
    ensures lset_subset(lset_empty(), s) == true;
{
}

lemma void lset_subset_empty_r<t>(list<t> s)
    requires true;
    ensures lset_subset(s, lset_empty()) == (s == lset_empty());
{
    switch(s) {
        case nil:
        case cons(h,t):
    }    
}

lemma void lset_subset_add_l<t>(list<t> s1, t el, list<t> s2)
    requires true;
    ensures lset_subset(lset_add(s1, el), s2) == (lset_contains(s2, el) && lset_subset(s1, s2));
{
}

lemma void lset_subset_add_r<t>(list<t> s1, list<t> s2, t el)
    requires lset_subset(s1, s2) == true;
    ensures lset_subset(s1, lset_add(s2, el)) == true;
{
    switch(s1) {
        case nil:
        case cons(h,t):
            lset_subset_add_r(t, s2, el);
    }
}

lemma void lset_subset_remove_l<t>(list<t> s1, t el, list<t> s2)
    requires lset_subset(s1, s2) == true;
    ensures lset_subset(lset_remove(s1, el), s2) == true;
{
    switch(s1) {
        case nil:
        case cons(h,t):
            lset_subset_remove_l(t, el, s2);
    }    
}

lemma void lset_subset_remove_r<t>(list<t> s1, list<t> s2, t el)
    requires true;
    ensures lset_subset(s1, lset_remove(s2, el)) == (!lset_contains(s1, el) && lset_subset(s1, s2));
{
    switch(s1) {
        case nil:
        case cons(h,t):
            lset_remove_contains(s2, el, h);
            lset_subset_remove_r(t, s2, el);
    }    
}

lemma void lset_subset_union_l<t>(list<t> s1, list<t> s2)
    requires true;
    ensures lset_subset(s1, lset_union(s1, s2)) == true;
{
    switch(s1) {
        case nil: 
        case cons(h, t):
            lset_subset_union_l(t, s2);
            lset_subset_add_r(t, lset_union(t, s2), h);
    }
}

lemma void lset_subset_union_r<t>(list<t> s1, list<t> s2)
    requires true;
    ensures lset_subset(s2, lset_union(s1, s2)) == true;
{
    switch(s1) {
        case nil: lset_subset_refl(s2);
        case cons(h, t):
            lset_subset_union_r(t, s2);
            lset_subset_add_r(s2, lset_union(t, s2), h);
    }
}

lemma void lset_subset_inters_l<t>(list<t> s1, list<t> s2)
    requires true;
    ensures lset_subset(lset_inters(s1, s2), s1) == true;
{
    switch(s1) {
        case nil: 
        case cons(h, t):
            lset_subset_inters_l(t, s2);
            lset_add_remains_subset(lset_inters(t, s2), t, h);
    }
}

lemma void lset_subset_inters_r<t>(list<t> s1, list<t> s2)
    requires true;
    ensures lset_subset(lset_inters(s1, s2), s2) == true;
{
    switch(s1) {
        case nil: 
        case cons(h, t):
            lset_subset_inters_r(t, s2);
    }
}
//subset is reflexive and transitive

lemma void lset_subset_refl<t>(list<t> s)
    requires true;
    ensures lset_subset(s, s) == true;
{
    switch(s){
        case nil:
        case cons(h,t):
            lset_subset_refl(t);
            lset_subset_add_r(t, t, h);
    }
}

lemma void lset_subset_trans<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_subset(s1, s2) == true &*& lset_subset(s2, s3) == true;
    ensures lset_subset(s1, s3) == true;
{
    switch(s1) {
        case nil:
        case cons(s1h, s1t):
            lset_subset_contains(s2, s3, s1h);
            lset_subset_trans(s1t, s2, s3);
    }

}

//subset is structurally compatible

lemma void lset_add_remains_subset<t>(list<t> s1, list<t> s2, t el)
    requires lset_subset(s1, s2) == true;
    ensures lset_subset(lset_add(s1, el), lset_add(s2, el)) == true;
{
    lset_subset_add_r(s1, s2, el);
}

lemma void lset_remove_remains_subset<t>(list<t> s1, list<t> s2, t el)
    requires lset_subset(s1, s2) == true;
    ensures lset_subset(lset_remove(s1, el), lset_remove(s2, el)) == true;
{
    switch(s1) {
        case nil:
        case cons(h,t):
            lset_remove_contains(s2, el, h);
            lset_remove_remains_subset(t, s2, el);
    }    
}

lemma void lset_union_r_remains_subset<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_subset(s1, s2) == true;
    ensures lset_subset(lset_union(s1, s3),lset_union(s2, s3)) == true;
{
    switch(s1) {
        case nil: lset_subset_union_r(s2, s3);
        case cons(h, t): 
            lset_union_r_remains_subset(t, s2, s3);
            lset_subset_contains(s1, s2, h);
            lset_union_contains(s2, s3, h);
    }
}

lemma void lset_union_l_remains_subset<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_subset(s2, s3) == true;
    ensures lset_subset(lset_union(s1, s2),lset_union(s1, s3)) == true;
{
    switch(s1) {
        case nil: 
        case cons(h, t): 
            lset_union_l_remains_subset(t, s2, s3);
            lset_add_remains_subset(lset_union(t, s2),lset_union(t, s3), h);
    }
}   

lemma void lset_inters_r_remains_subset<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_subset(s1, s2) == true;
    ensures lset_subset(lset_inters(s1, s3),lset_inters(s2, s3)) == true;
{
    switch(s1) {
        case nil: 
        case cons(h, t): 
            lset_inters_r_remains_subset(t, s2, s3);
            lset_subset_contains(s1, s2, h);
            lset_inters_contains(s2, s3, h);            
    }
}

lemma void lset_inters_l_remains_subset<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_subset(s2, s3) == true;
    ensures lset_subset(lset_inters(s1, s2),lset_inters(s1, s3)) == true;
{
    switch(s1) {
        case nil: 
        case cons(h, t): 
            lset_inters_l_remains_subset(t, s2, s3);
            lset_subset_contains(s2, s3, h);
            lset_inters_contains(s1, s3, h);
            lset_add_remains_subset(lset_inters(t, s2),lset_inters(t, s3), h);
    }
}

lemma void lset_diff_r_remains_subset<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_subset(s1, s2) == true;
    ensures lset_subset(lset_diff(s1, s3),lset_diff(s2, s3)) == true;
{
    switch(s1) {
        case nil: 
        case cons(h, t): 
            lset_diff_r_remains_subset(t, s2, s3);
            lset_subset_contains(s1, s2, h);
            lset_diff_contains(s2, s3, h);
    }
}

lemma void lset_diff_l_inverts_subset<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_subset(s2, s3) == true;
    ensures lset_subset(lset_diff(s1, s3), lset_diff(s1, s2)) == true;
{
    switch(s1) {
        case nil: 
        case cons(h, t): 
            lset_diff_l_inverts_subset(t, s2, s3);
            lset_subset_contains(s2, s3, h);
            lset_diff_contains(s1, s2, h);
            lset_add_remains_subset(lset_diff(t, s3),lset_diff(t, s2), h);
    }
}

//equality is an equivalence relation

lemma void lset_equals_refl<t>(list<t> s)
    requires true;
    ensures lset_equals(s, s) == true;
{
    lset_subset_refl(s);
}

lemma void lset_equals_sym<t>(list<t> s1, list<t> s2)
    requires true;
    ensures lset_equals(s1, s2) == lset_equals(s2, s1);
{
}

lemma void lset_equals_trans<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_equals(s1, s2) == true &*& lset_equals(s2, s3) == true;
    ensures lset_equals(s1, s3) == true;
{
    lset_subset_trans(s1, s2, s3);
    lset_subset_trans(s3, s2, s1);
}

//equality is a congruence

lemma void lset_add_remains_equals<t>(list<t> s1, list<t> s2, t el)
    requires lset_equals(s1, s2) == true;
    ensures lset_equals(lset_add(s1, el), lset_add(s2, el)) == true;
{
    lset_add_remains_subset(s1, s2, el);
    lset_add_remains_subset(s2, s1, el);
}

lemma void lset_remove_remains_equals<t>(list<t> s1, list<t> s2, t el)
    requires lset_equals(s1, s2) == true;
    ensures lset_equals(lset_remove(s1, el), lset_remove(s2, el)) == true;
{
    lset_remove_remains_subset(s1, s2, el);
    lset_remove_remains_subset(s2, s1, el);
}

lemma void lset_union_r_remains_equals<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_equals(s1, s2) == true;
    ensures lset_equals(lset_union(s1, s3),lset_union(s2, s3)) == true;
{
    lset_union_r_remains_subset(s1, s2, s3);
    lset_union_r_remains_subset(s2, s1, s3);    
}

lemma void lset_union_l_remains_equals<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_equals(s2, s3) == true;
    ensures lset_equals(lset_union(s1, s2),lset_union(s1, s3)) == true;
{
    lset_union_l_remains_subset(s1, s2, s3);
    lset_union_l_remains_subset(s1, s3, s2);
}   

lemma void lset_inters_r_remains_equals<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_equals(s1, s2) == true;
    ensures lset_equals(lset_inters(s1, s3),lset_inters(s2, s3)) == true;
{
    lset_inters_r_remains_subset(s1, s2, s3);
    lset_inters_r_remains_subset(s2, s1, s3);
}

lemma void lset_inters_l_remains_equals<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_equals(s2, s3) == true;
    ensures lset_equals(lset_inters(s1, s2),lset_inters(s1, s3)) == true;
{
    lset_inters_l_remains_subset(s1, s2, s3);
    lset_inters_l_remains_subset(s1, s3, s2);
}

lemma void lset_diff_r_remains_equals<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_equals(s1, s2) == true;
    ensures lset_equals(lset_diff(s1, s3),lset_diff(s2, s3)) == true;
{
    lset_diff_r_remains_subset(s1, s2, s3);
    lset_diff_r_remains_subset(s2, s1, s3);
}
lemma void lset_diff_l_remains_equals<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_equals(s2, s3) == true;
    ensures lset_equals(lset_diff(s1, s2),lset_diff(s1, s3)) == true;
{
    lset_diff_l_inverts_subset(s1, s2, s3);
    lset_diff_l_inverts_subset(s1, s3, s2);
}    

lemma void lset_equals_remains_subset_r<t>(list<t> s1, list<t>  s2, list<t> s3)
    requires lset_equals(s2, s3) == true;
    ensures lset_subset(s1, s2) == lset_subset(s1, s3); 
{
    if(lset_subset(s1, s2)) {
        lset_subset_trans(s1, s2, s3);
    } else if(lset_subset(s1, s3)) {
        lset_subset_trans(s1, s3, s2);
    }
}

lemma void lset_equals_remains_subset_l<t>(list<t> s1, list<t> s2, list<t> s3)
    requires lset_equals(s1, s2) == true;
    ensures lset_subset(s1, s3) == lset_subset(s2, s3); 
{
    if(lset_subset(s1, s3)) {
        lset_subset_trans(s2, s1, s3);
    } else if(lset_subset(s2, s3)) {
        lset_subset_trans(s1, s2, s3);
    }
}


lemma void lset_equals_remains_disjoint_l<t>(list<t> s1, list<t>  s2, list<t> s3)
    requires lset_equals(s1, s2) == true;
    ensures lset_disjoint(s1, s3) == lset_disjoint(s2, s3); 
{
    lset_inters_r_remains_equals(s1, s2, s3);
    if(lset_inters(s1, s3) == nil) {
        lset_equals_empty_l(lset_inters(s2, s3));
    } else if (lset_inters(s2, s3) == nil) {
        lset_equals_empty_r(lset_inters(s1, s3));
    }
    
}

lemma void lset_equals_remains_disjoint_r<t>(list<t> s1, list<t>  s2, list<t> s3)
    requires lset_equals(s2, s3) == true;
    ensures lset_disjoint(s1, s2) == lset_disjoint(s1, s3); 
{
    lset_inters_l_remains_equals(s1, s2, s3);
    if(lset_inters(s1, s2) == nil) {
        lset_equals_empty_l(lset_inters(s1, s3));
    } else if (lset_inters(s1, s3) == nil) {
        lset_equals_empty_r(lset_inters(s1, s2));
    }
}

// commutativity lemma's
lemma void lset_union_comm_singleton_r<t>(list<t> s1, t el)
    requires true;
    ensures lset_equals(lset_union(s1, lset_singleton(el)), lset_union(lset_singleton(el), s1)) == true;
{
    switch(s1) {
        case nil:
        case cons(h, t):
            lset_union_comm_singleton_r(t, el);
            lset_add_assoc(t, el, h);
            lset_add_remains_equals(lset_union(t, lset_singleton(el)), lset_union(lset_singleton(el), t), h);
            lset_equals_trans(lset_union(s1, lset_singleton(el)), lset_add(lset_union(lset_singleton(el), t), h), lset_union(lset_singleton(el), s1));
    }
}    



lemma void lset_union_comm<t>(list<t> s1, list<t> s2)
    requires true;
    ensures lset_equals(lset_union(s1, s2), lset_union(s2, s1)) == true; 
{
    switch(s1) {
        case nil: lset_equals_refl(s2);
        case cons(h, t):
            lset_union_set_add_r(s2, t, h);
            lset_union_comm_singleton_r(s2, h);
            lset_union_r_remains_equals(lset_union(s2, lset_singleton(h)), lset_add(s2, h), t);            
            lset_union_comm(t, s2);
            lset_add_remains_equals(lset_union(t, s2), lset_union(s2, t), h);
            lset_equals_trans(lset_union(s1, s2), lset_add(lset_union(s2, t), h),lset_union(s2, s1));
    }
}


lemma void lset_add_equals<t>(list<t> s, t v)
    requires lset_contains(s, v) == true;
    ensures lset_equals(lset_add(s, v), s) == true;
{
    lset_equals_refl(s);
    lset_subset_add_r(s,s,v);
}
predicate gres<t>(t v) = true;

lemma void lset_contains_equals_set_add<t>(list<t> s, t v)
    requires lset_contains(s, v) == true;
    ensures gres(?s2) &*& lset_equals(s, lset_add(s2, v)) == true;
{
    switch(s) {
        case nil:
        case cons(h, t):
             if(h == v) {
                 close gres(t);
                 lset_equals_refl(lset_add(t, v));
             } else {
                 lset_contains_equals_set_add(t, v);
                 open gres(?s3);
                 lset_add_remains_equals(t, lset_add(s3, v), h);
                 lset_add_assoc(s3, v, h); 
                 lset_equals_trans(s, lset_add(lset_add(s3, v), h), lset_add(lset_add(s3, h), v));
                 close gres(cons(h, s3));
             }
    } 
}

lemma void lset_inters_add_r<t>(list<t> s1, list<t> s2, t v);
    requires true;
    ensures lset_subset(lset_inters(s1, s2), lset_inters(s1, lset_add(s2, v))) == true ;
    
lemma void lset_inters_comm_helper<t>(list<t> s1, list<t> s2)
    requires true;
    ensures lset_subset(lset_inters(s1, s2), lset_inters(s2, s1)) == true; 
{
    switch(s1) {
        case nil:  lset_inters_empty_r(s2);
        case cons(h, t):
            lset_inters_comm_helper(t, s2);
            lset_inters_contains(s2, s1, h);
            lset_inters_add_r(s2, t, h);
            lset_subset_trans(lset_inters(t, s2), lset_inters(s2, t), lset_inters(s2, cons(h, t)));
    }
}

lemma void lset_inters_comm<t>(list<t> s1, list<t> s2)
    requires true;
    ensures lset_equals(lset_inters(s1, s2), lset_inters(s2, s1)) == true; 
{
    lset_inters_comm_helper(s1, s2);
    lset_inters_comm_helper(s2, s1);
}

// associativity lemma's

lemma void lset_add_assoc<t>(list<t> s, t e1, t e2)
    requires true;
    ensures lset_equals(lset_add(lset_add(s, e1),e2), lset_add(lset_add(s, e2),e1)) == true;
{
    lset_subset_refl(s);
    lset_subset_add_r(s, s, e2);
    lset_subset_add_r(s, lset_add(s, e2), e1);
    lset_subset_add_r(s, s, e1);
    lset_subset_add_r(s, lset_add(s, e1), e2);
}

lemma void lset_remove_assoc<t>(list<t> s, t e1, t e2)
    requires true;
    ensures lset_equals(lset_remove(lset_remove(s, e1),e2), lset_remove(lset_remove(s, e2),e1)) == true;
{
    switch(s) {
        case nil:
        case cons(h, t):
            lset_remove_assoc(t, e1, e2);
            if(h != e1 && h != e2) {
                lset_add_remains_equals(lset_remove(lset_remove(t, e1),e2), lset_remove(lset_remove(t, e2),e1), h);
            }
    }
}

lemma void lset_union_assoc<t>(list<t> s1, list<t> s2, list<t> s3)
    requires true;
    ensures lset_equals(lset_union(s1, lset_union(s2, s3)), lset_union(lset_union(s1, s2), s3)) == true; 
{
    switch(s1) {
        case nil: lset_equals_refl(lset_union(s2, s3));
        case cons(h,t):
            lset_union_assoc(t, s2, s3);
            lset_add_remains_equals(lset_union(t, lset_union(s2, s3)), lset_union(lset_union(t, s2), s3), h);
    }
}

lemma void lset_inters_assoc<t>(list<t> s1, list<t> s2, list<t> s3)
    requires true;
    ensures lset_equals(lset_inters(s1, lset_inters(s2, s3)), lset_inters(lset_inters(s1, s2), s3)) == true; 
{
    switch(s1) {
        case nil: 
        case cons(h,t):
            lset_inters_assoc(t, s2, s3);
            lset_add_remains_equals(lset_inters(t, lset_inters(s2, s3)), lset_inters(lset_inters(t, s2), s3), h);
            lset_inters_contains(s2, s3, h);
    }
    
}

//-------------------------------------------------------------------------------------------------------------------------------------------------------
//refactor from here
lemma void lset_remove_ident<t>(list<t> s, t el)
    requires !lset_contains(s, el);
    ensures lset_remove(s, el) == s;
{
    switch(s) {
        case nil:
        case cons(h,t):
            lset_remove_ident(t, el);
    }    
}




// equality 


lemma void lset_equals_empty_l<t>(list<t> s)
    requires true;
    ensures lset_equals(lset_empty(), s) == (s==lset_empty());
{
    lset_subset_empty_r(s);
}

lemma void lset_equals_empty_r<t>(list<t> s)
    requires true;
    ensures lset_equals(s, lset_empty()) == (s==lset_empty());
{
    lset_subset_empty_r(s);
}


lemma void lset_equals_add_l_remove_r<t>(list<t> s1, list<t> s2, t el)
    requires lset_equals(lset_add(s1, el), s2) == true &*& !lset_contains(s1, el);
    ensures lset_equals(s1, lset_remove(s2, el)) == true;
{
    lset_remove_remains_equals(lset_add(s1, el), s2, el);
    lset_remove_ident(s1, el);
    lset_remove_contains(s2, el, el);
    lset_remove_ident(lset_remove(s2, el), el);
}

lemma void lset_equals_add_r_remove_l<t>(list<t> s1, list<t> s2, t el)
    requires lset_equals(s1, lset_add(s2, el)) == true &*& !lset_contains(s2, el);
    ensures lset_equals(lset_remove(s1, el), s2) == true;
{
    lset_equals_add_l_remove_r(s2, s1, el);
}


    
        



// more advanced

lemma void lset_union_subset_l<t>(list<t> s1, list<t> s2, list<t> s3)
    requires true;
    ensures lset_subset(lset_union(s1, s2), s3) == (lset_subset(s1, s3) && lset_subset(s2, s3));
{
    switch(s1) {
        case nil:
        case cons(h,t):
            lset_union_subset_l(t, s2, s3);
    }
}


lemma void lset_inters_distr_union<t>(list<t> s1, list<t> s2, list<t> s3)
    requires true;
    ensures lset_equals(lset_inters(s1, lset_union(s2, s3)), lset_union(lset_inters(s1, s2), lset_inters(s1, s3))) == true; 
{
    if(!lset_equals(lset_inters(s1, lset_union(s2, s3)), lset_union(lset_inters(s1, s2), lset_inters(s1, s3)))) {
        lset_equals_contains_conv(lset_inters(s1, lset_union(s2, s3)), lset_union(lset_inters(s1, s2), lset_inters(s1, s3)));
        open exwitness(?v);
        lset_union_contains(s2, s3, v);
        lset_inters_contains(s1, lset_union(s2, s3), v);
        lset_inters_contains(s1, s2, v);
        lset_inters_contains(s1, s3, v);
        lset_union_contains(lset_inters(s1, s2), lset_inters(s1, s3), v);
        assert false;
    }
}

lemma void lset_union_distr_inters<t>(list<t> s1, list<t> s2, list<t> s3)
    requires true;
    ensures lset_equals(lset_union(s1, lset_inters(s2, s3)), lset_inters(lset_union(s1, s2), lset_union(s1, s3))) == true; 
{
    if(!lset_equals(lset_union(s1, lset_inters(s2, s3)), lset_inters(lset_union(s1, s2), lset_union(s1, s3)))) {
        lset_equals_contains_conv(lset_union(s1, lset_inters(s2, s3)), lset_inters(lset_union(s1, s2), lset_union(s1, s3)));
        open exwitness(?v);
        lset_inters_contains(s2, s3, v);
        lset_union_contains(s1, lset_inters(s2, s3), v);
        lset_union_contains(s1, s2, v);
        lset_union_contains(s1, s3, v);
        lset_inters_contains(lset_union(s1, s2), lset_union(s1, s3), v);
        assert false;
    }
}
*/

@*/