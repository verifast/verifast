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

fixpoint int len(intlist v) {
  switch (v) {
    case nil: return 0;
    case cons(x, v): return 1 + len(v);
  }
}

fixpoint int ith(intlist v, int i) {
  switch (v) {
    case nil: return 0;
    case cons(x, v): return (i == 0 ? x : ith(v, i - 1));
  }
}
@*/

/*@

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
  //@ close node(n, n->next, n->value);
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
  //@ close node(n, n->next, n->value);
  struct node *l = list->last;
  //@ open node(l, _, _);
  l->next = n;
  l->value = x;
  //@ close node(l, n, x);
  list->last = n;
  //@ lseg_add(list->first, l, n);
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
      lseg_append(n1->next, n2, n3);
      close node(n1, n1->next, n1->value);
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
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ close node(l1, f2->next, f2->value);
    //@ close lseg(l1, l2, _v2);
    //@ lseg_append(list1->first, l1, l2);
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
@*/

int length(struct llist *list)
  //@ requires llist(list, ?_v);
  //@ ensures llist(list, _v) &*& result == len(_v);
{
  //@ open llist(list, _v);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ close lseg(f, f, nil);
  while (n != l)
    //@ invariant lseg(f, n, ?_ls1) &*& lseg(n, l, ?_ls2) &*& node(l, _, _) &*& _v == list_append(_ls1, _ls2) &*& c + len(_ls2) == len(_v);
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
    c = c + 1;
    //@ add_append_lemma(_ls1, value, ls3);
  }
  //@ open lseg(n, l, _ls2);
  //@ list_append_nil(_ls1);
  //@ close llist(list, _v);
  return c;
}

/*@
fixpoint intlist drop(int i, intlist v) {
  switch (v) {
    case nil: return nil;
    case cons(x, v): return i == 0 ? cons(x, v) : drop(i - 1, v);
  }
}

lemma void drop_ith(intlist v, int i, int h)
  requires 0 <= i &*& i < len(v) &*& ith(drop(i, v), 0) == h;
  ensures ith(v, i) == h;
{
  switch (v) {
    case nil:
    case cons(x, v): if (i == 0) { } else { drop_ith(v, i - 1, h); }
  }
}

lemma void drop_0_lemma(intlist v)
  requires true;
  ensures drop(0,v) == v;
{
  switch (v) {
    case nil:
    case cons(x, v):
  }
}

lemma void drop_len_lemma(int i, intlist v)
  requires 0 <= i &*& i <= len(v);
  ensures len(drop(i, v)) == len(v) - i;
{
  switch (v) {
    case nil:
    case cons(h, t):
      if (i == 0) {
      } else {
        drop_len_lemma(i - 1, t);
      }
  }
}

lemma void drop_cons_lemma(int i, intlist v, int h, intlist t)
  requires 0 <= i &*& drop(i, v) == cons(h, t);
  ensures drop(i + 1, v) == t;
{
  switch (v) {
    case nil:
    case cons(h2, t2):
      if (i == 0) {
        drop_0_lemma(v);
        if (1 == 0) { } else { drop_0_lemma(t); }
      } else {
        drop_cons_lemma(i - 1, t2, h, t);
        if (i + 1 == 0) { } else { }
      }
  }
}
@*/

int lookup(struct llist *list, int index)
  //@ requires llist(list, ?_v) &*& 0 <= index &*& index < len(_v);
  //@ ensures llist(list, _v) &*& result == ith(_v, index);
{
  //@ open llist(list, _);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ close lseg(f, n, nil);
  //@ drop_0_lemma(_v);
  while (i < index)
    //@ invariant 0 <= i &*& i <= index &*& lseg(f, n, ?_ls1) &*& lseg(n, l, ?_ls2) &*& _v == list_append(_ls1, _ls2) &*& _ls2 == drop(i, _v) &*& i + len(_ls2) == len(_v);
  {
    //@ drop_len_lemma(i, _v);
    //@ open lseg(n, l, _);
    //@ open node(n, _, _);
    struct node *next = n->next;
    //@ int value = n->value;
    //@ close node(n, next, value);
    //@ open lseg(next, l, ?ls3); // To produce a witness node for next.
    //@ lseg_add(f, n, next);
    //@ close lseg(next, l, ls3);
    //@ drop_cons_lemma(i, _v, value, ls3);
    n = next;
    i = i + 1;
    //@ add_append_lemma(_ls1, value, ls3);
  }
  //@ open lseg(n, l, _ls2);
  //@ open node(n, ?nnext, _);
  int value = n->value;
  //@ close node(n, nnext, value);
  //@ close lseg(n, l, _ls2);
  //@ lseg_append(f, n, l);
  //@ close llist(list, _v);
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
  int n = length(l1); assert(n == 5);
  int e0 = lookup(l1, 0); assert(e0 == 10);
  int e1 = lookup(l1, 1); assert(e1 == 20);
  int e2 = lookup(l1, 2); assert(e2 == 30);
  int e3 = lookup(l1, 3); assert(e3 == 50);
  int e4 = lookup(l1, 4); assert(e4 == 60);
  dispose(l1);
  return 0;
}
