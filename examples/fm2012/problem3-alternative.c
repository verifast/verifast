struct tree {
  int data;
  struct tree* left;
  struct tree* right;
};

/*@
inductive tree = empty | tree(int, tree, tree);

predicate tree(struct tree* t; tree tr) =
  t == 0 ?
    tr == empty
  :
    t->left |-> ?l &*& tree(l, ?trl) &*&
    t->right |-> ?r &*& tree(r, ?trr) &*&
    t->data |-> ?v &*& malloc_block_tree(t) &*&
    tr == tree(v, trl, trr);
    
lemma_auto void tree_zero()
  requires tree(?t, ?tr);
  ensures tree(t, tr) &*& (t == 0 ? tr == empty : true);
{
  open tree(t, tr);
}
    
predicate tree_with_hole(struct tree* t, struct tree* hole; tree tr) =
  hole != 0 &*&
  (t == hole ?
    tr == empty
  :
    t != 0 &*& t->left |-> ?l &*& tree_with_hole(l, hole, ?trl) &*&
    t->right |-> ?r &*& tree(r, ?trr) &*&
    t->data |-> ?v &*& malloc_block_tree(t) &*&
    tr == tree(v, trl, trr) &*& hole != 0
  );

lemma_auto void tree_with_hole_zero()
  requires tree_with_hole(?t, ?hole, ?tr);
  ensures tree_with_hole(t, hole, tr) &*& hole != 0;
{
  open tree_with_hole(t, hole, tr);
}

fixpoint int leftmost(tree tr) {
  switch(tr) {
    case empty: return 0;
    case tree(v, l, r): return l == empty ? v : leftmost(l);
  }
}

fixpoint tree merge(tree t1, tree holet) {
  switch(t1) {
    case empty: return holet;
    case tree(v, l, r): return tree(v, merge(l, holet), r); 
  }
}

lemma void merge_tree(struct tree* t, struct tree* hole)
  requires tree_with_hole(t, hole, ?hollow_tr) &*& tree(hole, ?tr);
  ensures tree(t, merge(hollow_tr, tr)) ;
{
  open tree_with_hole(t, hole, hollow_tr);
  if(t == hole) {
  } else {
    merge_tree(t->left, hole);
    
  }
}

fixpoint tree delete_leftmost(tree t) {
  switch(t) {
    case empty: return empty;
    case tree(v, l, r): 
     return l == empty ? r : tree(v, delete_leftmost(l), r);
  }
}

lemma void merge_non_empty(tree hollow, tree hole)
  requires hole != empty;
  ensures merge(hollow, hole) != empty;
{
  switch(hollow) 
  {
    case empty:
    case tree(v, l, r):
      merge_non_empty(l, hole);
  }
}

lemma void delete_leftmost_merge(tree hollow, tree hole)
  requires hole != empty;
  ensures delete_leftmost(merge(hollow, hole)) == merge(hollow, delete_leftmost(hole));
{
  switch(hollow) {
    case empty:
    case tree(v, l, r):
      delete_leftmost_merge(l, hole);
      merge_non_empty(l, hole);
  }
}

lemma void leftmost_merge(tree hollow, tree hole)
  requires hole != empty;
  ensures leftmost(merge(hollow, hole)) == leftmost(hole);
{
  switch(hollow) {
    case empty:
    case tree(v, l, r):
      merge_non_empty(l, hole);
      leftmost_merge(l, hole);
  }
}
@*/

void search_tree_delete_min(struct tree* t, struct tree** res, int* min)
  //@ requires tree(t, ?tr) &*& tr != empty &*& pointer(res, _) &*& integer(min, _);
  //@ ensures pointer(res, ?rest) &*& tree(rest, delete_leftmost(tr)) &*& integer(min, leftmost(tr));
{
  struct tree* tt, pp, p;
  int m;
  //@ open tree(t, tr);
  p = t->left;
  //@ open tree(p, _);
  if (p == 0) {
    m = t->data; tt = t->right; free (t); t = tt;
  } else {
    pp = t; tt = p->left;
    //@ close tree_with_hole(pp, pp, empty);
    //@ open tree(tt, _);
    //@ close tree(tt, _);
    while (tt != 0)
      /*@ requires tree_with_hole(pp, pp, empty) &*& pp != 0 &*& pp->left |-> p &*& pp->right |-> ?ppr &*& tree(ppr, ?pprtree) &*& pp->data |-> ?ppd &*&  malloc_block_tree(pp) &*&
                   p != 0 &*& p->left |-> tt &*& p->right |-> ?pr &*& tree(pr, ?prtree) &*& tree(tt, ?tttree) &*& p->data |-> ?pd &*& malloc_block_tree(p);
      @*/
      /*@ ensures  pp != 0 &*& pp->left |-> p &*& pp->right |-> ?nppr &*& tree(nppr, ?npprtree) &*& pp->data |-> ?nppd &*&  malloc_block_tree(pp) &*&
                      p != 0 &*& p->left |-> tt &*& p->right |-> ?npr &*& tree(npr, ?nprtree) &*& p->data |-> ?npd &*& malloc_block_tree(p) &*& tree_with_hole(old_pp, pp, ?hollow_tree) &*& tt == 0 &*&
                      merge(hollow_tree, tree(nppd, tree(npd, empty, nprtree), npprtree)) == tree(ppd, tree(pd, tttree, prtree), pprtree);
      @*/
    {
      pp = p; p = tt; tt = p->left;
      //@ close tree_with_hole(pp, pp, empty);
      //@ recursive_call();
    }
    m = p->data; tt = p->right; free(p); pp->left= tt;
    //@ merge_tree(t, pp);
    //@ delete_leftmost_merge(hollow_tree, tree(nppd, tree(npd, empty, nprtree), npprtree));
    //@ leftmost_merge(hollow_tree, tree(nppd, tree(npd, empty, nprtree), npprtree));     
   }
   *res = t;
   *min = m;
}

/*@
fixpoint bool tree_contains(tree t, int x) {
  switch(t) {
    case empty: return false;
    case tree(v, l, r): return v == x || tree_contains(l, x) || tree_contains(r, x); 
  }
}

fixpoint int mathmin(int x, int y) {
  return x <= y ? x : y;
}

fixpoint int mathmax(int x, int y) {
  return x >= y ? x : y;
}

fixpoint int tree_min(tree t) {
  switch(t) {
    case empty: return 0;
    case tree(v, l, r):
      return l == empty ? 
        (r == empty ? v : mathmin(v, tree_min(r)))
      :
        (r == empty ? mathmin(v, tree_min(l)) : mathmin(v, mathmin(tree_min(l), tree_min(r))));  
  }
}

fixpoint int tree_max(tree t) {
  switch(t) {
    case empty: return 0;
    case tree(v, l, r):
      return l == empty ? 
        (r == empty ? v : mathmax(v, tree_max(r)))
      :
        (r == empty ? mathmax(v, tree_max(l)) : mathmax(v, mathmax(tree_max(l), tree_max(r))));  
  }
}

fixpoint bool in_order(tree t) {
  switch(t) {
    case empty: return true;
    case tree(v, l, r):
      return (l == empty ? true : v >= tree_max(l)) && (r == empty ? true : v <= tree_min(r)) && in_order(l) && in_order(r);
  }
}

/*lemma void delete_leftmost(tree tr)
  requires tr != empty &*& in_order(tr) == true;
  ensures delete_leftmost(tr) == empty ? true : tree_max(tr) == tree_max(delete_leftmost(tr));
{
  switch(tr) {
    case empty:
    case tree(v, l, r):
      if(l != empty) {
        delete_leftmost(l);
        assume(false);
      } else {
        
      }
  }
}*/

lemma void tree_min_le_tree_max(tree tr)
  requires true;
  ensures tree_min(tr) <= tree_max(tr);
{
  switch(tr) {
    case empty:
    case tree(v, l, r):
      tree_min_le_tree_max(l);
      tree_min_le_tree_max(r);
  }
}

lemma void tree_max_delete_leftmost(tree tr) 
  requires tr != empty &*& delete_leftmost(tr) != empty &*& in_order(tr) == true;
  ensures tree_max(delete_leftmost(tr)) == tree_max(tr);
{
  switch(tr) {
    case empty:
    case tree(v, l, r):
      if(l == empty) {
        if(r == empty) {
        } else {
          assert delete_leftmost(tr) == r;
          assert tree_max(tr) == v || tree_max(tr) == tree_max(r);
          tree_min_le_tree_max(r);
        }
      } else {
        assume(false);
        tree_max_delete_leftmost(l);
        if(r == empty) {
          assert tree_max(tr) == v || tree_max(tr) == tree_max(l);
          
        } else {
        }
      }
  }
} 

lemma void delete_leftmost_preserves_in_order(tree tr)
  requires in_order(tr) == true &*& tr != empty;
  ensures true == in_order(delete_leftmost(tr));
{
  switch(tr) {
    case empty:
    case tree(v, l, r): 
      if(l == empty) {
      } else {
        delete_leftmost_preserves_in_order(l);
        if(delete_leftmost(l) == empty) {
        } else {
          tree_max_delete_leftmost(l); 
        }
      }
  }
}

/*lemma void tree_min_contains(tree tr, int x)
  requires tree_contains(tr, x) == true;
  ensures tree_min(tr) <= x;
{
  switch(tr) {
    case empty:
    case tree(v, l, r):
      assume(false);
      if(tree_contains(l, x)) {
        tree_max_contains(l, x);
      }
      if(tree_contains(r, x)) {
        tree_max_contains(r, x);
      }
  }
}

lemma void tree_max_contains(tree tr, int x)
  requires tree_contains(tr, x) == true;
  ensures x <= tree_max(tr);
{
  switch(tr) {
    case empty:
    case tree(v, l, r):
      assume(false);
      if(tree_contains(l, x)) {
        tree_max_contains(l, x);
      }
      if(tree_contains(r, x)) {
        tree_max_contains(r, x);
      }
  }
}

lemma void min_value_contains(tree tr, int x)
  requires in_order(tr) == true &*& tree_contains(tr, x) == true;
  ensures min_value(tr) <= x;
{
  switch(tr) {
    case empty:
    case tree(v, l, r):
      if(tree_contains(l, x)) {
        tree_max_contains(l, x);
        min_value_contains(l, x);
      }
      if(tree_contains(r, x)) {
        tree_min_contains(r, x);
        min_value_contains(r, x);
      }
  }
}*/
@*/

struct tree* test(struct tree* t, int x)
  //@ requires tree(t, ?tr) &*& tr != empty &*& tree_contains(tr, x) == true &*& in_order(tr) == true;
  //@ ensures tree(result, _); 
{
  struct tree* res;
  int min;
  search_tree_delete_min(t, &res, &min);
 // assert(min <= x);
  return res;
}