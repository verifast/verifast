struct tree { Tree left; int data; Tree right; };
typedef struct tree *Tree;

/*@
inductive tree = empty | node(Tree, tree, int, tree);

fixpoint tree delete_min(tree t) {
    switch (t) {
        case empty: return empty;
        case node(p, t1, v, t2): return t1 == empty ? t2 : node(p, delete_min(t1), v, t2);
    }
}
fixpoint int min_value(tree vs) {
    switch (vs) {
        case empty: return 0;
        case node(p, t1, v, t2): return t1 == empty ? v : min_value(t1);
    }
}
fixpoint Tree p_(tree t) {
    switch (t) {
        case empty: return 0;
        case node(p, l, v, r): return p;
    }
}

predicate Tree(Tree t; tree vs) =
    t == 0 ?
        vs == empty
    :
        t->left |-> ?l &*& Tree(l, ?vsl) &*& t->right |-> ?r &*& Tree(r, ?vsr) &*&
        t->data |-> ?v &*& malloc_block_tree(t) &*& vs == node(t, vsl, v, vsr);

predicate Tree_r(Tree t; int v, tree rvs) =
    t->data |-> v &*& malloc_block_tree(t) &*& t->right |-> ?r &*& Tree(r, rvs);

lemma_auto void Tree_inv()
    requires Tree(?t, ?vs);
    ensures Tree(t, vs) &*& t == p_(vs);
{ open Tree(_, _); }

typedef lemma void fill_hole_lemma(predicate() pred, Tree t, tree vs, Tree pp, Tree r)();
    requires pred() &*& pp->left |-> r;
    ensures Tree(t, delete_min(vs));

fixpoint bool sorted_between(int min, tree t, int max) {
    switch (t) {
        case empty: return true;
        case node(p, t1, v, t2): return min <= v && v <= max && sorted_between(min, t1, v) && sorted_between(v, t2, max);
    }
}

lemma void sorted_between_weaken(int min0, int min1, tree t, int max0, int max1)
    requires sorted_between(min1, t, max0) == true &*& min0 <= min1 &*& max0 <= max1;
    ensures sorted_between(min0, t, max1) == true;
{
    switch (t) {
        case empty:
        case node(p, t1, v, t2):
            sorted_between_weaken(min0, min1, t1, v, v);
            sorted_between_weaken(v, v, t2, max0, max1);
    }
}

lemma_auto void delete_min_sorted_between(int min, tree t, int max)
    requires sorted_between(min, t, max) == true;
    ensures sorted_between(min, delete_min(t), max) == true;
{
    switch (t) {
        case empty:
        case node(p, t1, v, t2):
            if (t1 != empty) {
                delete_min_sorted_between(min, t1, v);
            } else {
                sorted_between_weaken(min, v, t2, max, max);
            }
    }
}

fixpoint bool sorted(tree t) { return sorted_between(INT_MIN, t, INT_MAX); }
@*/

void search_tree_delete_min(Tree t, Tree *r1, int *r2)
    //@ requires Tree(t, ?vs) &*& vs != empty &*& *r1 |-> _ &*& *r2 |-> _ &*& sorted(vs) == true;
    //@ ensures *r1 |-> ?tresult &*& Tree(tresult, delete_min(vs)) &*& *r2 |-> min_value(vs) &*& sorted(delete_min(vs)) == true;
{
    //@ open Tree(_, _);
    if (t->left == 0) { /*@ open Tree(0, _); @*/ *r2 = t->data; *r1 = t->right; free(t); } else {
        Tree pp = t; Tree p = pp->left; Tree tt = p->left;
        for (;;)
            /*@ requires Tree(pp, ?vs_) &*& vs_ == node(pp, ?lvs, ?v, ?rvs) &*&
                    lvs == node(p, ?llvs, _, ?rlvs) &*& tt == p_(llvs); @*/
            /*@ ensures p->left |-> _ &*& p->data |-> min_value(vs_) &*& p->right |-> ?r &*&
                    malloc_block_tree(p) &*&
                    is_fill_hole_lemma(_, ?pred, old_pp, vs_, pp, r) &*& pred() &*& pp->left |-> p; @*/
        {
            //@ { open Tree(pp, _); open Tree(p, _); open Tree(tt, _); }
            if (tt == 0) {
                /*@ {
                    predicate P() = Tree_r(pp, v, rvs) &*& Tree(p_(rlvs), rlvs);
                    lemma void lem()
                        requires P() &*& pp->left |-> p_(rlvs);
                        ensures Tree(pp, delete_min(vs_));
                    { open P(); }
                    produce_lemma_function_pointer_chunk(lem) : fill_hole_lemma(P, pp, vs_, pp, p_(rlvs))()
                    { call(); };
                    close P();
                } @*/
                break;
            }
            pp = p; p = tt; tt = p->left;
            //@ recursive_call();
            //@ assert is_fill_hole_lemma(?lem0, ?P0, _, _, ?pp_, ?r);
            /*@ {
                predicate P() =
                    Tree_r(old_pp, v, rvs) &*& old_pp->left |-> old_p &*&
                    is_fill_hole_lemma(lem0, P0, p_(lvs), lvs, pp_, r) &*& P0();
                lemma void lem()
                    requires P() &*& pp->left |-> r;
                    ensures Tree(old_pp, delete_min(vs_));
                {
                    open P();
                    lem0();
                    leak is_fill_hole_lemma(_, _, _, _, _, _);
                }
                produce_lemma_function_pointer_chunk(lem) : fill_hole_lemma(P, old_pp, vs_, pp_, r)()
                { call(); };
                close P();
            } @*/
        }
        *r1 = t; *r2 = p->data; tt = p->right; free(p); pp->left = tt;
        //@ assert is_fill_hole_lemma(?lem, _, _, _, _, _);
        //@ lem();
        //@ leak is_fill_hole_lemma(_, _, _, _, _, _);
    }
}
