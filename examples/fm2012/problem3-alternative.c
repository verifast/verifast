struct tree {
  int data;
  struct tree* left;
  struct tree* right;
};

/*@
inductive tree = empty | tree(int, tree, tree);

predicate tree_single(struct tree* t; int data, struct tree* left, struct tree* right) =
  t != 0 &*& t->data |-> data &*&
  t->left |-> left &*& t->right |-> right &*&
  malloc_block_tree(t);
  
lemma_auto void treesingle_non_zero()
  requires tree_single(?t, ?data, ?left, ?right);
  ensures tree_single(t, data, left, right) &*& t != 0;
{
  open tree_single(t, data, left, right);
}

predicate tree(struct tree* t; tree tr) =
  t == 0 ?
    tr == empty
  :
    tree_single(t, ?data, ?left, ?right) &*&
    tree(left, ?lt) &*& tree(right, ?rt) &*&
    tr == tree(data, lt, rt);
    
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
  
fixpoint tree delete_leftmost(tree t) {
  switch(t) {
    case empty: return empty;
    case tree(v, l, r): 
     return l == empty ? r : tree(v, delete_leftmost(l), r);
  }
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
  p = t->left;
  if (p == 0) {
    m = t->data; tt = t->right; free (t); t = tt;
  } else {
    pp = t; tt = p->left;
    while (tt != 0)
      /*@ requires tree_single(pp, ?ppd, p, ?ppr) &*& tree(ppr, ?pprtree) &*& 
                   tree_single(p, ?pd, tt, ?pr) &*& tree(tt, ?tttree) &*& tree(pr, ?prtree);
      @*/
      /*@ ensures  tree_single(pp, ?nppd, p, ?nppr) &*& tree(nppr, ?npprtree) &*&
                   tree_single(p, ?npd, tt, ?npr) &*& tree_with_hole(old_pp, pp, ?hollow_tree) &*& tree(npr, ?nprtree) &*&
                   merge(hollow_tree, tree(nppd, tree(npd, empty, nprtree), npprtree)) == tree(ppd, tree(pd, tttree, prtree), pprtree);
      @*/
    {
      //@ open tree_single(pp, ppd, p, ppr);
      pp = p; p = tt; tt = p->left;
      //@ recursive_call();
      //@ open tree_single(pp, _, _, _);
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
  requires tr != empty &*& in_order(tr) == true;
  ensures delete_leftmost(tr) == empty || tree_max(delete_leftmost(tr)) == tree_max(tr);
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
        tree_max_delete_leftmost(l);
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

lemma void tree_min_le_all(tree tr, int x)
  requires tree_contains(tr, x) == true;
  ensures tree_min(tr) <= x;
{
  switch(tr) {
    case empty:
    case tree(v, l, r):
      if(v == x) {
      } else if(tree_contains(l, x)) {
        tree_min_le_all(l, x);
      } else {
        tree_min_le_all(r, x);
      }
  }
}

lemma void leftmost_eq_min(tree tr)
  requires tr != empty &*& in_order(tr) == true;
  ensures leftmost(tr) == tree_min(tr);
{
  switch(tr) {
    case empty:
    case tree(v, l, r):
      if(l == empty) {
      } else {
        leftmost_eq_min(l);
        tree_min_le_tree_max(l);
      }  
  }
}
@*/

struct tree* test(struct tree* t, int x)
  //@ requires tree(t, ?tr) &*& tr != empty &*& tree_contains(tr, x) == true &*& in_order(tr) == true;
  //@ ensures tree(result, ?ntr) &*& in_order(ntr) == true; 
{
  struct tree* res;
  int min;
  search_tree_delete_min(t, &res, &min);
  //@ delete_leftmost_preserves_in_order(tr);
  //@ leftmost_eq_min(tr);
  //@ tree_min_le_all(tr, x);
  assert min <= x;
  return res;
}