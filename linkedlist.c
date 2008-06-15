struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

//@ predicate node(struct node *node, struct node *next, int value)
//@   requires node->next |-> next &*& node->value |-> value &*& malloc_block(node);

//@ inductive intlist = nil | cons(int, intlist);

//@ fixpoint int len(intlist v) {
//@   switch (v) {
//@     case nil: return 0;
//@     case cons(x, v): return 1 + len(v);
//@   }
//@ }

//@ fixpoint int ith(intlist v, int i) {
//@   switch (v) {
//@     case nil: return 0;
//@     case cons(x, v): return (i == 0 ? x : ith(v, i - 1));
//@   }
//@ }

//@ predicate lseg(struct node *n1, struct node *n2, intlist v)
//@   requires switch (v) { case nil: return n1 == n2; case cons(x, v): return node(n1, _n, x) &*& lseg(_n, n2, v); };

//@ predicate llist(struct llist *list, intlist v)
//@   requires list->first |-> _f &*& list->last |-> _l &*& lseg(_f, _l, v) &*& node(_l, _, _) &*& malloc_block(list);

struct llist *create_llist()
//@   requires true;
//@   ensures llist(result, nil);
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

//@ fixpoint int list_add(intlist v, int x) {
//@   switch (v) {
//@     case nil: return cons(x, nil);
//@     case cons(y, v): return cons(y, list_add(v, x));
//@   }
//@ }

//@ lemma void lseg_add(struct node *n1, struct node *n2, struct node *n3)
//@   requires lseg(n1, n2, _v) &*& node(n2, n3, _x);
//@   ensures lseg(n1, n3, list_add(_v, _x));
//@ {
//@   open lseg(n1, n2, _v);
//@   if (n1 == n2) {
//@   } else {
//@     lseg_add(n1->next, n2, n3);
//@   }
//@   close lseg(n1, n3, list_add(_v, _x);
//@ }

void add(struct llist *list, int x)
//@   requires llist(list, _v);
//@   ensures llist(list, list_add(_v, x));
{
  //@ open llist(list, _v);
  struct node *n = malloc(sizeof(struct node));
  //@ close node(n, n->next, n->value);
  struct node *l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ lseg_add(list->first, l, n);
  //@ close llist(list, list_add(_v, x));
}

//@ fixpoint intlist list_append(intlist l1, intlist l2) {
//@   switch (l1) {
//@     case nil: return l2;
//@     case cons(x, v): return cons(x, list_append(v, l2));
//@   }
//@ }

//@ lemma void lseg_append(struct node *n1, struct node *n2, struct node *n3)
//@   requires lseg(n1, n2, _v1) &*& lseg(n2, n3, _v2);
//@   ensures lseg(n1, n3, list_append(_v1, _v2));
//@ {
//@   open lseg(n1, n2, _v1);
//@   if (n1 == n2) {
//@   } else {
//@     lseg_append(n1->next, n2, n3);
//@   }
//@   close lseg(n1, n3, list_append(_v1, _v2));
//@ }

void append(struct llist *list1, struct llist *list2)
//@   requires llist(list1, _v1) &*& llist(list2, _v2);
//@   ensures llist(list1, list_append(_v1, _v2));
{
//@   open llist(list1, _v1);
//@   open llist(list2, _v2);
  struct llist *l = list1->last;
  struct llist *f = list2->first;
//@   open lseg(f, list2->last, _v2);  // Causes case split.
//@   open node(l, _);
//@   open node(f, _);
  l->next = f->next;
  l->value = f->value;
  list1->last = list2->last;
//@   close lseg(l, list2->last, _v2);
//@   lseg_append(list1->first, l, list2->last);
//@   close llist(list1, list_append(_v1, _v2));
  free(f);
  free(list2);
}

void dispose(struct llist *list)
//@   requires llist(list, _);
//@   ensures emp;
{
  //@ open llist(list, _);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant lseg(n, l, _);
  {
    //@ open lseg(n, l, _);
    //@ open node(n, _);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open node(l, _);
  free(l);
  free(list);
}

int length(struct llist *list)
//@   requires llist(list, _v);
//@   ensures llist(list, _v) &*& result == len(_v);
{
  //@ open llist(list, _v);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  while (n != l)
    //@ invariant lseg(f, n, _ls1) &*& lseg(n, l, _ls2) &*& _v = list_append(_ls1, _ls2) &*& c + len(_ls2) == len(_v);
  {
    //@ open lseg(n, l, _);
    //@ open node(n, _, _);
    struct node *next = n->next;
    //@ close node(n, n->next, n->value);
    //@ close lseg(next, l, _);
    //@ lseg_add(f, n, next);
    n = next;
    c = c + 1;
  }
  //@ close llist(list, _v);
  return c;
}

//@ fixpoint intlist drop(int i, intlist v) {
//@   switch (v) {
//@     case nil: return nil;
//@     case cons(x, v): i == 0 ? cons(x, v) : drop(i - 1, v);
//@   }
//@ }

//@ lemma void drop_ith(intlist v, int i)
//@   requires 0 <= i && i < len(v);
//@   ensures ith(v, i) == ith(0, drop(i, v));
//@ {
//@   switch (v) {
//@     case nil: return;
//@     case cons(x, v): drop_ith(v, i - 1); return;
//@   }
//@ }

int lookup(struct llist *list, int index)
  //@ requires llist(list, _v) &*& 0 <= index &*& index < len(_v);
  //@ ensures llist(list, _v) &*& result == ith(_v, index);
{
  //@ open llist(list, _);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  while (i < index)
    //@ invariant i <= index &*& lseg(f, n, _ls1) &*& lseg(n, l, _ls2) &*& _v = list_append(_ls1, _ls2) &*& _ls2 == drop(i, _v);
  {
    //@ open lseg(n, l, _);
    //@ open node(n, _, _);
    struct node *next = n->next;
    //@ close node(n, _, _);
    //@ close lseg(next, l, _);
    //@ lseg_add(f, n, next);
    n = n->next;
    i = i + 1;
  }
  //@ drop_ith(_v, index);
  return n->value;
}

void main()
  //@ requires emp;
  //@ ensures emp;
{
  struct llist *l1 = create_list();
  struct llist *l2 = create_list();
  add(l1, 10);
  add(l1, 20);
  add(l1, 30);
  add(l2, 40);
  add(l2, 50);
  add(l2, 60);
  append(l1, l2);
  assert(length(l1) == 6);
  assert(lookup(l1, 0) == 10);
  assert(lookup(l1, 1) == 20);
  assert(lookup(l1, 2) == 30);
  assert(lookup(l1, 3) == 40);
  assert(lookup(l1, 4) == 50);
  assert(lookup(l1, 5) == 60);
  dispose(l1);
}
