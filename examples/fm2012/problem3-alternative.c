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
        t != 0 &*& t->left |-> ?l &*& Tree(l, ?vsl) &*&
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

/*@
predicate Tree_with_hole(Tree t, Tree hole; tree_ vs) =
    hole != 0 &*&
    t == hole ?
        vs == empty
    :
        t != 0 &*& t->left |-> ?l &*& Tree_with_hole(l, hole, ?vsl) &*&
        t->right |-> ?r &*& Tree(r, ?vsr) &*&
        t->data |-> ?v &*& malloc_block_tree(t) &*&
        vs == node(vsl, t, v, vsr);
        
fixpoint tree_ merge(tree_ t1, tree_ t2) {
  switch(t1) {
    case empty: return t2;
    case node(l, p, v, r): return node(merge(l, t2), p, v, r); 
  }
}

lemma void move_hole(struct tree* t)
  requires Tree_with_hole(t, ?hole, ?vs1) &*& Tree(hole, node(?left, hole, ?v, ?right)) &*& getptr(left) != 0;
  ensures Tree_with_hole(t, getptr(left), merge(vs1, node(empty, hole, v, right))) &*& Tree(getptr(left), left) &*&
          merge(vs1, node(left, hole, v, right)) == merge(merge(vs1, node(empty, hole, v, right)), left);
{
  open Tree_with_hole(t, hole, vs1);
  open Tree(hole, _);
  open Tree(getptr(left), _);
  if(t == hole) {
    close Tree_with_hole(t, getptr(left), merge(vs1, node(empty, hole, v, right)));
  } else {
    move_hole(t->left);
    close Tree_with_hole(t, getptr(left), merge(vs1, node(empty, hole, v, right)));
  }
}

lemma void plug_hole(struct tree* t1, struct tree* t2)
  requires Tree_with_hole(t1, t2, ?vs1) &*& Tree(t2, ?vs2);
  ensures Tree(t1, merge(vs1, vs2)) ;
{
  open Tree_with_hole(t1, t2, vs1);
  open Tree(t2, vs2);
  if(t1 == t2) {
  } else {
    plug_hole(t1->left, t2);
    close Tree(t1, merge(vs1, vs2));
  }
}

lemma void delete_min_merge(tree_ t1, tree_ t2)
  requires t2 != empty;
  ensures merge(t1, t2) != empty &*&
          delete_min(merge(t1, t2)) == merge(t1, delete_min(t2)) &*&
          min_value(merge(t1, t2)) == min_value(t2);
{
  switch(t1) {
    case empty:
    case node(l, p, v, r):
      delete_min_merge(l, t2);
  }
}
@*/

void search_tree_delete_min(struct tree* t, struct tree** r1, int* r2)
  //@ requires Tree(t, ?vs) &*& vs != empty &*& pointer(r1, _) &*& integer(r2, _) &*& ordered_between(INT_MIN, vs, INT_MAX) == true;
  //@ ensures pointer(r1, ?tresult) &*& Tree(tresult, delete_min(vs)) &*& integer(r2, min_value(vs)) &*& ordered_between(INT_MIN, vs, INT_MAX) == true;
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
      /*@ invariant Tree_with_hole(t, pp, ?vs1) &*& Tree(pp, ?vs2) &*& getptr(getleft(vs2)) == p &*& 
                    p != 0 &*& getptr(getleft(getleft(vs2))) == tt &*& vs == merge(vs1, vs2);
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
    m = p->data; tt = p->right; free(p); pp->left= tt;
    //@ plug_hole(t, pp);
    //@ delete_min_merge(vs1, vs2); 
   }
   *r1 = t;
   *r2 = m;
}