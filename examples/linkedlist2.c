struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/*@
predicate node(struct node *node, struct node *next, int value)
  requires node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);

inductive intlist = | nil | cons(int, intlist);

predicate lseg(struct node *n1, struct node *n2, intlist v)
  requires n1 == n2 ? emp &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list, intlist v)
  requires list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _) &*& malloc_block_llist(list);
@*/

struct llist *create_llist()
  //@ requires emp;
  //@ ensures llist(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  struct node *n = malloc(sizeof(struct node));
  //@ struct node *next = n->next;
  //@ int value = n->value;
  //@ close node(n, next, value);
  //@ close lseg(n, n, nil);
  l->first = n;
  l->last = n;
  //@ close llist(l, nil);
  return l;
}

/*@
fixpoint intlist list_add(intlist v, int x) {
  switch (v) {
    case nil: return cons(x, nil);
    case cons(y, v): return cons(y, list_add(v, x));
  }
}

lemma void distinct_nodes(struct node *n1, struct node *n2)
  requires node(n1, ?n1n, ?n1v) &*& node(n2, ?n2n, ?n2v);
  ensures node(n1, n1n, n1v) &*& node(n2, n2n, n2v) &*& n1 != n2;
{
  open node(n1, _, _);
  open node(n2, _, _);
  close node(n1, n1n, n1v);
  close node(n2, n2n, n2v);
}

lemma void lseg_add(struct node *n1, struct node *n2, struct node *n3)
  requires lseg(n1, n2, ?_v) &*& node(n2, n3, ?_x) &*& node(n3, ?n3next, ?n3value);
  ensures lseg(n1, n3, list_add(_v, _x)) &*& node(n3, n3next, n3value);
{
  distinct_nodes(n2, n3);
  open lseg(n1, n2, _v);
  if (n1 == n2) {
    close lseg(n3, n3, nil);
  } else {
    distinct_nodes(n1, n3);
    open node(n1, ?next, ?value);
    lseg_add(next, n2, n3);
    close node(n1, next, value);
  }
  
  close lseg(n1, n3, list_add(_v, _x));
}
@*/

void add(struct llist *list, int x)
  //@ requires llist(list, ?_v);
  //@ ensures llist(list, list_add(_v, x));
{
  //@ open llist(list, _v);
  struct node *n = malloc(sizeof(struct node));
  //@ struct node *next = n->next;
  //@ int value = n->value;
  //@ close node(n, next, value);
  //@ struct node *f = list->first;
  struct node *l = list->last;
  //@ open node(l, _, _);
  l->next = n;
  l->value = x;
  //@ close node(l, n, x);
  list->last = n;
  //@ lseg_add(f, l, n);
  //@ close llist(list, list_add(_v, x));
}

/*@
fixpoint intlist list_append(intlist l1, intlist l2) {
  switch (l1) {
    case nil: return l2;
    case cons(x, v): return cons(x, list_append(v, l2));
  }
}

lemma void lseg_append(struct node *n1, struct node *n2, struct node *n3)
  requires lseg(n1, n2, ?_v1) &*& lseg(n2, n3, ?_v2) &*& node(n3, ?n3n, ?n3v);
  ensures lseg(n1, n3, list_append(_v1, _v2)) &*& node(n3, n3n, n3v);
{
  open lseg(n1, n2, _v1);
  switch (_v1) {
    case nil:
    case cons(x, v):
      distinct_nodes(n1, n3);
      open node(n1, _, _);
      struct node *next = n1->next;
      int value = n1->value;
      lseg_append(next, n2, n3);
      close node(n1, next, value);
      close lseg(n1, n3, list_append(_v1, _v2));
  }
}

lemma void list_append_nil(intlist v)
  requires emp;
  ensures list_append(v, nil) == v;
{
  switch (v) {
    case nil:
    case cons(h, t):
      list_append_nil(t);
  }
}
@*/

void append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?_v1) &*& llist(list2, ?_v2);
  //@ ensures llist(list1, list_append(_v1, _v2));
{
  //@ open llist(list1, _v1);
  //@ open llist(list2, _v2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  //@ open lseg(f2, l2, _v2);  // Causes case split.
  if (f2 == l2) {
    //@ open node(l2, _, _);
    free(l2);
    free(list2);
    //@ list_append_nil(_v1);
    //@ close llist(list1, _v1);
  } else {
    //@ distinct_nodes(l1, l2);
    //@ open node(l1, _, _);
    //@ open node(f2, _, _);
    struct node *next = f2->next;
    l1->next = next;
    int value = f2->value;
    l1->value = value;
    list1->last = l2;
    //@ close node(l1, next, value);
    //@ close lseg(l1, l2, _v2);
    //@ struct node *f1 = list1->first;
    //@ lseg_append(f1, l1, l2);
    //@ close llist(list1, list_append(_v1, _v2));
    free(f2);
    free(list2);
  }
}

void dispose(struct llist *list)
  //@ requires llist(list, _);
  //@ ensures emp;
{
  //@ open llist(list, _);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant lseg(n, l, _);
  {
    //@ open lseg(n, l, _);
    //@ open node(n, _, _);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open lseg(n, n, _);  // Clean up empty lseg.
  //@ open node(l, _, _);
  free(l);
  free(list);
}

/*@
lemma void add_append_lemma(intlist v1, int x, intlist v2)
  requires emp;
  ensures list_append(v1, cons(x, v2)) == list_append(list_add(v1, x), v2);
{
  switch (v1) {
    case nil:
    case cons(h, t):
      add_append_lemma(t, x, v2);
  }
}

fixpoint uint len(intlist v) {
  switch (v) {
    case nil: return zero;
    case cons(x, v): return succ(len(v));
  }
}

fixpoint int ifzero_int(uint n, int n1, int n2) {
  switch (n) {
    case zero: return n1;
    case succ(n): return n2;
  }
}

fixpoint uint minus_one(uint n) {
  switch (n) {
    case zero: return zero;
    case succ(n): return n;
  }
}

fixpoint int ith(intlist v, uint i) {
  switch (v) {
    case nil: return 0;
    case cons(x, v): return ifzero_int(i, x, ith(v, minus_one(i)));
  }
}

fixpoint uint plus(uint n1, uint n2) {
  switch (n1) {
    case zero: return n2;
    case succ(n): return plus(n, succ(n2));
  }
}

lemma void plus_succ(uint n1, uint n2)
  requires emp;
  ensures plus(succ(n1), n2) == succ(plus(n1, n2));
{
  switch (n1) {
    case zero:
    case succ(n):
      plus_succ(n, succ(n2));
  }
}

lemma void plus_zero(uint n)
  requires emp;
  ensures plus(n, zero) == n;
{
  switch (n) {
    case zero:
    case succ(m):
      plus_succ(m, zero);
      plus_zero(m);
  }
}

@*/

uint length(struct llist *list)
  //@ requires llist(list, ?_v);
  //@ ensures llist(list, _v) &*& result == len(_v);
{
  //@ open llist(list, _v);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  uint c = zero;
  //@ close lseg(f, f, nil);
  while (n != l)
    //@ invariant lseg(f, n, ?_ls1) &*& lseg(n, l, ?_ls2) &*& node(l, _, _) &*& _v == list_append(_ls1, _ls2) &*& plus(c, len(_ls2)) == len(_v);
  {
    //@ open lseg(n, l, _ls2);
    //@ open node(n, _, _);
    struct node *next = n->next;
    //@ int value = n->value;
    //@ close node(n, next, value);
    //@ open lseg(next, l, ?ls3); // To produce a witness node for next.
    //@ lseg_add(f, n, next);
    //@ close lseg(next, l, ls3);
    n = next;
    c = succ(c);
    //@ add_append_lemma(_ls1, value, ls3);
  }
  //@ open lseg(n, l, _ls2);
  //@ list_append_nil(_ls1);
  //@ close llist(list, _v);
  //@ plus_zero(c);
  return c;
}

/*@

fixpoint intlist ifzero_intlist(uint n, intlist l1, intlist l2) {
  switch (n) {
    case zero: return l1;
    case succ(n): return l2;
  }
}

fixpoint intlist drop(uint i, intlist v) {
  switch (v) {
    case nil: return nil;
    case cons(x, v): return ifzero_intlist(i, cons(x, v), drop(minus_one(i), v));
  }
}

fixpoint bool ifzero_bool(uint n, bool b1, bool b2) {
  switch (n) {
    case zero: return b1;
    case succ(n): return b2;
  }
}

fixpoint bool lessthan(uint n1, uint n2) {
  switch (n2) {
    case zero: return false;
    case succ(n2): return ifzero_bool(n1, true, lessthan(minus_one(n1), n2));
  }
}

lemma void drop_ith(intlist v, uint i, int h)
  requires lessthan(i, len(v)) == true &*& ith(drop(i, v), zero) == h;
  ensures ith(v, i) == h;
{
  switch (v) {
    case nil:
    case cons(x, v):
      switch (i) {
        case zero:
        case succ(i):
          drop_ith(v, i, h);
      }
  }
}

lemma void drop_0_lemma(intlist v)
  requires emp;
  ensures drop(zero,v) == v;
{
  switch (v) {
    case nil:
    case cons(x, v):
  }
}

lemma void less_than_succ(uint x, uint y)
  requires lessthan(x, y) == true;
  ensures lessthan(x, succ(y)) == true;
{
  switch (y) {
    case zero:
    case succ(y0):
      switch (x) {
        case zero:
        case succ(x0):
          less_than_succ(x0, y0);
      }
  }
}

lemma void less_than_trans(uint x, uint y, uint z)
  requires lessthan(x, y) == true &*& lessthan(y, z) == true;
  ensures lessthan(x, z) == true;
{
  switch (y) {
    case zero:
    case succ(y0):
      switch (z) {
        case zero:
        case succ(z0):
          switch (x) {
            case zero:
            case succ(x0):
              less_than_trans(x0, y0, z0);
          }
      }
  }
}

lemma void less_than_succ_trans(uint x, uint y, uint z)
  requires lessthan(x, y) == true &*& lessthan(y, z) == true;
  ensures lessthan(succ(x), z) == true;
{
  switch (y) {
    case zero:
    case succ(y0):
      switch (z) {
        case zero:
        case succ(z0):
          switch (x) {
            case zero:
              switch (z0) {
                case zero:
                case succ(z00):
              }
            case succ(x0):
              less_than_succ_trans(x0, y0, z0);
          }
      }
  }
}


lemma void drop_succ_lemma(uint i, intlist v)
  requires lessthan(i, len(v)) == true;
  ensures len(drop(i, v)) == succ(len(drop(succ(i), v)));
{
  switch (v) {
    case nil:
    case cons(h, t):
      switch (i) {
        case zero:
        case succ(j):
          drop_succ_lemma(j, t);
      }
      switch (t) {
        case nil:
        case cons(ht, tt):
      }
  }
}

lemma void drop_len_lemma(uint i, intlist v)
  requires lessthan(i, len(v)) == true;
  ensures plus(i, len(drop(i, v))) == len(v);
{
  switch (i) {
    case zero:
      switch (v) {
        case nil:
        case cons(h, t):
      }
    case succ(j):
      switch (v) {
        case nil:
        case cons(h, t):
          less_than_succ(j, len(t));
      }
      drop_len_lemma(j, v);
      drop_succ_lemma(j, v);
  }
}

lemma void drop_cons_lemma(uint i, intlist v, int h, intlist t)
  requires drop(i, v) == cons(h, t);
  ensures drop(succ(i), v) == t;
{
  switch (v) {
    case nil:
    case cons(h2, t2):
      switch (i) {
        case zero:
          drop_0_lemma(v);
          drop_0_lemma(t);
        case succ(i):
          drop_cons_lemma(i, t2, h, t);
      }
  }
}

fixpoint bool le(uint x, uint y) {
  switch (x) {
    case zero: return true;
    case succ(x0): return ifzero_bool(y, false, le(x0, minus_one(y)));
  }
}

lemma void lessthan_neq(uint x, uint y)
  requires lessthan(x, y) == true;
  ensures x != y;
{
  switch (y) {
    case zero:
    case succ(y0):
      switch (x) {
        case zero:
        case succ(x0):
          lessthan_neq(x0, y0);
      }
  }
}

lemma void lessthan_le(uint x, uint y)
  requires lessthan(x, y) == true;
  ensures le(succ(x), y) == true;
{
  switch (y) {
    case zero:
    case succ(y0):
      switch (x) {
        case zero:
        case succ(x0):
          lessthan_le(x0, y0);
      }
  }
}

lemma void le_not_lessthan(uint x, uint y)
  requires le(x, y) == true &*& lessthan(x, y) != true;
  ensures x == y;
{
  switch (x) {
    case zero:
      switch (y) {
        case zero:
        case succ(y0):
      }
    case succ(x0):
      switch (y) {
        case zero:
        case succ(y0):
          le_not_lessthan(x0, y0);
      }
  }
}
@*/

int lookup(struct llist *list, uint index)
  //@ requires llist(list, ?_v) &*& lessthan(index, len(_v)) == true;
  //@ ensures llist(list, _v) &*& result == ith(_v, index);
{
  //@ open llist(list, _);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  uint i = zero;
  //@ close lseg(f, n, nil);
  //@ drop_0_lemma(_v);
  while (lessthan(i, index) == true)
    //@ invariant le(i, index) == true &*& lseg(f, n, ?_ls1) &*& lseg(n, l, ?_ls2) &*& _v == list_append(_ls1, _ls2) &*& _ls2 == drop(i, _v) &*& plus(i, len(_ls2)) == len(_v);
  {
    //@ less_than_trans(i, index, len(_v));
    //@ drop_len_lemma(i, _v);
    //@ plus_zero(i);
    //@ lessthan_neq(i, len(_v));
    //@ open lseg(n, l, _);
    //@ open node(n, _, _);
    struct node *next = n->next;
    //@ int value = n->value;
    //@ close node(n, next, value);
    //@ open lseg(next, l, ?ls3); // To produce a witness node for next.
    //@ less_than_succ_trans(i, index, len(_v));
    //@ lessthan_neq(succ(i), len(_v));
    //@ plus_zero(succ(i));
    //@ lseg_add(f, n, next);
    //@ close lseg(next, l, ls3);
    //@ drop_cons_lemma(i, _v, value, ls3);
    n = next;
    //@ lessthan_le(i, index);
    i = succ(i);
    //@ add_append_lemma(_ls1, value, ls3);
  }
  //@ open lseg(n, l, _ls2);
  //@ open node(n, ?nnext, _);
  int value = n->value;
  //@ close node(n, nnext, value);
  //@ close lseg(n, l, _ls2);
  //@ lseg_append(f, n, l);
  //@ close llist(list, _v);
  //@ le_not_lessthan(i, index);
  //@ plus_zero(index);
  //@ lessthan_neq(index, len(_v));
  //@ drop_ith(_v, index, value);
  return value;
}

int removeFirst(struct llist *l)
  //@ requires llist(l, ?v) &*& v != nil;
  //@ ensures llist(l, ?t) &*& v == cons(result, t);
{
  //@ open llist(l, v);
  struct node *nf = l->first;
  //@ open lseg(nf, ?nl, v);
  //@ open node(nf, _, _);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ open lseg(nfn, nl, ?t); // Just to get t
  //@ close lseg(nfn, nl, t);
  //@ close llist(l, t);
  return nfv;
}

void main0()
  //@ requires emp;
  //@ ensures emp;
{
  struct llist *l = create_llist();
  add(l, 10);
  add(l, 20);
  add(l, 30);
  add(l, 40);
  int x1 = removeFirst(l);
  assert(x1 == 10);
  int x2 = removeFirst(l);
  assert(x2 == 20);
  dispose(l);
}

int main()
  //@ requires emp;
  //@ ensures emp;
{
  struct llist *l1 = create_llist();
  struct llist *l2 = create_llist();
  add(l1, 10);
  add(l1, 20);
  add(l1, 30);
  add(l2, 40);
  add(l2, 50);
  add(l2, 60);
  int x = removeFirst(l2); assert(x == 40);
  append(l1, l2);
  uint n = length(l1); assert(n == succ(succ(succ(succ(succ(zero))))));
  int e0 = lookup(l1, zero); assert(e0 == 10);
  int e1 = lookup(l1, succ(zero)); assert(e1 == 20);
  int e2 = lookup(l1, succ(succ(zero))); assert(e2 == 30);
  int e3 = lookup(l1, succ(succ(succ(zero)))); assert(e3 == 50);
  int e4 = lookup(l1, succ(succ(succ(succ(zero))))); assert(e4 == 60);
  dispose(l1);
  return 0;
}
