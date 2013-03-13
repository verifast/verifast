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

/*@
predicate Tree_with_hole(Tree t, Tree hole; tree vs) =
  hole != 0 &*&
  t == hole ?
    vs == empty
  :
    t != 0 &*& t->left |-> ?l &*& Tree_with_hole(l, hole, ?vsl) &*&
    t->right |-> ?r &*& Tree(r, ?vsr) &*&
    t->data |-> ?v &*& malloc_block_tree(t) &*&
    vs == node(t, vsl, v, vsr);
        
fixpoint tree merge(tree t1, tree t2) {
  switch(t1) {
    case empty: return t2;
    case node(p, l, v, r): return node(p, merge(l, t2), v, r); 
  }
}

lemma void move_hole(Tree t)
  requires Tree_with_hole(t, ?hole, ?vs1) &*& Tree(hole, node(hole, ?left, ?v, ?right)) &*& p_(left) != 0;
  ensures Tree_with_hole(t, p_(left), merge(vs1, node(hole, empty, v, right))) &*& Tree(p_(left), left) &*&
          merge(vs1, node(hole, left, v, right)) == merge(merge(vs1, node(hole, empty, v, right)), left);
{
  open Tree_with_hole(t, hole, vs1);
  open Tree(hole, _);
  open Tree(p_(left), _);
  if(t == hole) {
    close Tree_with_hole(t, p_(left), merge(vs1, node(hole, empty, v, right)));
  } else {
    move_hole(t->left);
    close Tree_with_hole(t, p_(left), merge(vs1, node(hole, empty, v, right)));
  }
}

lemma void plug_hole(Tree t1, Tree t2)
  requires Tree_with_hole(t1, t2, ?vs1) &*& Tree(t2, ?vs2);
  ensures Tree(t1, merge(vs1, vs2));
{
  open Tree_with_hole(t1, t2, vs1);
  open Tree(t2, vs2);
  if(t1 == t2) {
  } else {
    plug_hole(t1->left, t2);
    close Tree(t1, merge(vs1, vs2));
  }
}

lemma void delete_min_merge(tree t1, tree t2)
  requires t2 != empty;
  ensures merge(t1, t2) != empty &*&
          delete_min(merge(t1, t2)) == merge(t1, delete_min(t2)) &*&
          min_value(merge(t1, t2)) == min_value(t2);
{
  switch(t1) {
    case empty:
    case node(p, l, v, r):
      delete_min_merge(l, t2);
  }
}
@*/

void search_tree_delete_min(Tree t, Tree* r1, int* r2)
  //@ requires Tree(t, ?vs) &*& vs != empty &*& *r1 |-> _ &*& *r2 |-> _ &*& sorted(vs) == true;
  //@ ensures *r1 |-> ?tresult &*& Tree(tresult, delete_min(vs)) &*& *r2 |-> min_value(vs) &*& sorted(delete_min(vs)) == true;
{
  Tree tt, pp, p;
  int m;
  //@ open Tree(t, vs);
  p = t->left;
  if (p == 0) {
    //@ open Tree(p, _);
    m = t->data; tt = t->right; free (t); t = tt;
  } else {
    pp = t; tt = p->left;
    while (tt != 0)
      /*@ invariant Tree_with_hole(t, pp, ?vs1) &*& Tree(pp, ?vs2) &*& vs2 == node(pp, ?lvs, _, _) &*&
                    lvs == node(p, ?llvs, _, _) &*& p_(llvs) == tt &*& vs == merge(vs1, vs2);
      @*/
    {
      //@ open Tree(pp, vs2);
      //@ open Tree(pp->left, _);
      pp = p; p = tt; tt = p->left;
      //@ move_hole(t);
    }
    //@ open Tree(pp, _);
    //@ open Tree(pp->left, _);
    //@ open Tree(tt, _);
    m = p->data; tt = p->right; free(p); pp->left = tt;
    //@ plug_hole(t, pp);
    //@ delete_min_merge(vs1, vs2); 
  }
  *r1 = t;
  *r2 = m;
}