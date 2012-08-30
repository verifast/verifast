struct tree {
    Tree left;
    int data;
    Tree right;
};

typedef struct tree *Tree;

/*@

inductive tree_ = empty | node(tree_, Tree, int, tree_);

fixpoint tree_ delete_min(tree_ t) {
    switch (t) {
        case empty: return empty;
        case node(t1, p, v, t2): return t1 == empty ? t2 : node(delete_min(t1), p, v, t2);
    }
}

predicate Tree(Tree t; tree_ vs) =
    t == 0 ?
        vs == empty
    :
        t->left |-> ?l &*& Tree(l, ?vsl) &*&
        t->right |-> ?r &*& Tree(r, ?vsr) &*&
        t->data |-> ?v &*& malloc_block_tree(t) &*&
        vs == node(vsl, t, v, vsr);
        
lemma_auto void Tree_inv()
    requires Tree(?t, ?vs);
    ensures Tree(t, vs) &*& t == getptr(vs);
{
    open Tree(_, _);
}

fixpoint tree_ getleft(tree_ t) {
    switch (t) {
        case empty: return empty;
        case node(l, p, v, r): return l;
    }
}

fixpoint tree_ getright(tree_ t) {
    switch (t) {
        case empty: return empty;
        case node(l, p, v, r): return r;
    }
}

fixpoint int getvalue(tree_ t) {
    switch (t) {
        case empty: return 0;
        case node(l, p, v, r): return v;
    }
}


fixpoint Tree getptr(tree_ t) {
    switch (t) {
        case empty: return 0;
        case node(l, p, v, r): return p;
    }
}

typedef lemma void fill_hole_lemma(predicate() pred, Tree t, tree_ vs, Tree pp, Tree r)();
    requires pred() &*& pp->left |-> r;
    ensures Tree(t, delete_min(vs));

fixpoint int min_value(tree_ vs) {
    switch (vs) {
        case empty: return 0;
        case node(t1, p, v, t2): return t1 == empty ? v : min_value(t1);
    }
}

fixpoint bool ordered_between(int min, tree_ t, int max) {
    switch (t) {
        case empty: return true;
        case node(t1, p, v, t2): return min <= v && v <= max && ordered_between(min, t1, v) && ordered_between(v, t2, max);
    }
}

lemma void ordered_between_weaken(int min0, int min1, tree_ t, int max0, int max1)
    requires ordered_between(min1, t, max0) == true &*& min0 <= min1 &*& max0 <= max1;
    ensures ordered_between(min0, t, max1) == true;
{
    switch (t) {
        case empty:
        case node(t1, p, v, t2):
            ordered_between_weaken(min0, min1, t1, v, v);
            ordered_between_weaken(v, v, t2, max0, max1);
    }
}

lemma_auto void delete_min_ordered_between(int min, tree_ t, int max)
    requires ordered_between(min, t, max) == true;
    ensures ordered_between(min, delete_min(t), max) == true;
{
    switch (t) {
        case empty:
        case node(t1, p, v, t2):
            if (t1 != empty) {
                delete_min_ordered_between(min, t1, v);
            } else {
                ordered_between_weaken(min, v, t2, max, max);
            }
    }
}

@*/

void search_tree_delete_min(Tree t, Tree *r1, int *r2)
   //@ requires Tree(t, ?vs) &*& vs != empty &*& pointer(r1, _) &*& integer(r2, _) &*& ordered_between(INT_MIN, vs, INT_MAX) == true;
   //@ ensures pointer(r1, ?tresult) &*& Tree(tresult, delete_min(vs)) &*& integer(r2, min_value(vs)) &*& ordered_between(INT_MIN, delete_min(vs), INT_MAX) == true;
{
   Tree tt, pp, p;
   int m;
   //@ open Tree(_, _);
   p = t->left;
   if (p == 0) {
       //@ open Tree(0, _);
       m = t->data; tt = t->right; free (t); t = tt;
   } else {
       pp = t; tt = p->left;
       //while (tt != 0)
       for (;;)
           //@ requires Tree(pp, ?vs_) &*& pp != 0 &*& getptr(getleft(vs_)) == p &*& p != 0 &*& getptr(getleft(getleft(vs_))) == tt;
           //@ ensures is_fill_hole_lemma(_, ?pred, old_pp, vs_, pp, ?r) &*& pred() &*& pp->left |-> p &*& p->left |-> _ &*& p->data |-> min_value(vs_) &*& p->right |-> r &*& malloc_block_tree(p);
       {
           //@ open Tree(pp, _);
           //@ open Tree(p, _);
           //@ open Tree(tt, _);
           if (tt == 0) {
               {
                   /*@
                   predicate P() =
                       pp->data |-> getvalue(vs_) &*&
                       pp->right |-> getptr(getright(vs_)) &*& Tree(getptr(getright(vs_)), getright(vs_)) &*& 
                       malloc_block_tree(pp) &*&
                       Tree(getptr(getright(getleft(vs_))), getright(getleft(vs_)));
                   lemma void lem()
                       requires P() &*& pp->left |-> getptr(getright(getleft(vs_)));
                       ensures Tree(pp, delete_min(vs_));
                   {
                       open P();
                   }
                   @*/
                   //@ produce_lemma_function_pointer_chunk(lem) : fill_hole_lemma(P, pp, vs_, pp, getptr(getright(getleft(vs_))))() { call(); };
                   //@ close P();
               }
               break;
           }
           //@ Tree oldpp = pp;
           pp = p; p = tt; tt = p->left;
           //@ recursive_call();
           //@ assert is_fill_hole_lemma(?lem0, ?P0, _, _, ?pp_, ?r);
           /*@
           {
               predicate P() =
                   oldpp->data |-> getvalue(vs_) &*&
                   oldpp->left |-> getptr(getleft(vs_)) &*&
                   oldpp->right |-> getptr(getright(vs_)) &*& Tree(getptr(getright(vs_)), getright(vs_)) &*&
                   malloc_block_tree(oldpp) &*&
                   is_fill_hole_lemma(lem0, P0, getptr(getleft(vs_)), getleft(vs_), pp_, r) &*&
                   P0();
               lemma void lem()
                   requires P() &*& pp->left |-> r;
                   ensures Tree(oldpp, delete_min(vs_));
               {
                   open P();
                   lem0();
                   leak is_fill_hole_lemma(_, _, _, _, _, _);
               }
               produce_lemma_function_pointer_chunk(lem) : fill_hole_lemma(P, oldpp, vs_, pp_, r)() { call(); };
               close P();
           }
           @*/
       }
       m = p->data; tt = p->right; free(p); pp->left= tt;
       //@ assert is_fill_hole_lemma(?theLemma, _, _, _, _, _);
       //@ theLemma();
       //@ leak is_fill_hole_lemma(_, _, _, _, _, _);
   }
   //return (t,m);
   *r1 = t;
   *r2 = m;
}
