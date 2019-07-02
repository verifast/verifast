#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/*@
predicate node(struct node *node; struct node *next, int value) =
  node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? emp &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _) &*& malloc_block_llist(list);
@*/

struct llist *create_llist()
  //@ requires emp;
  //@ ensures llist(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  return l;
}

/*@
lemma void distinct_nodes(struct node *n1, struct node *n2)
  requires node(n1, ?n1n, ?n1v) &*& node(n2, ?n2n, ?n2v);
  ensures node(n1, n1n, n1v) &*& node(n2, n2n, n2v) &*& n1 != n2;
{
  open node(n1, _, _);
  open node(n2, _, _);
  close node(n1, _, _);
  close node(n2, _, _);
}

lemma void lseg_add(struct node *n2)
  requires lseg(?n1, n2, ?_v) &*& node(n2, ?n3, ?_x) &*& node(n3, ?n3next, ?n3value);
  ensures lseg(n1, n3, append(_v, cons(_x, nil))) &*& node(n3, n3next, n3value);
{
  distinct_nodes(n2, n3);
  open lseg(n1, n2, _v);
  if (n1 != n2) {
    distinct_nodes(n1, n3);
    open node(n1, _, _);
    lseg_add(n2);
    close node(n1, _, _);
  }
  
  close lseg(n1, n3, _);
}
@*/

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?_v);
  //@ ensures llist(list, append(_v, cons(x, nil)));
{
  struct node *l = 0;
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ lseg_add(l);
}

/*@
lemma void lseg_append(struct node *n1, struct node *n2, struct node *n3)
  requires lseg(n1, n2, ?_v1) &*& lseg(n2, n3, ?_v2) &*& node(n3, ?n3n, ?n3v);
  ensures lseg(n1, n3, append(_v1, _v2)) &*& node(n3, n3n, n3v);
{
  open lseg(n1, n2, _v1);
  switch (_v1) {
    case nil:
    case cons(x, v):
      distinct_nodes(n1, n3);
      open node(n1, _, _);
      lseg_append(n1->next, n2, n3);
      close node(n1, _, _);
      close lseg(n1, n3, _);
  }
}
@*/

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?_v1) &*& llist(list2, ?_v2);
  //@ ensures llist(list1, append(_v1, _v2));
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  //@ open lseg(f2, l2, _v2);  // Causes case split.
  if (f2 == l2) {
    free(l2);
    free(list2);
    //@ append_nil(_v1);
  } else {
    //@ distinct_nodes(l1, l2);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ close node(l1, l1->next, l1->value);
    //@ close lseg(l1, l2, _v2);
    //@ lseg_append(list1->first, l1, l2);
    //@ close llist(list1, append(_v1, _v2));
    free(f2);
    free(list2);
  }
}

void llist_dispose(struct llist *list)
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
  free(l);
  free(list);
}

/*@

predicate lseg2(struct node *first, struct node *last, struct node *final, list<int> v) =
  switch (v) {
    case nil: return first == last;
    case cons(head, tail):
      return first != final &*& node(first, ?next, head) &*& lseg2(next, last, final, tail);
  };

lemma void lseg2_add(struct node *first)
  requires [?f]lseg2(first, ?last, ?final, ?v) &*& [f]node(last, ?next, ?value) &*& last != final;
  ensures [f]lseg2(first, next, final, append(v, cons(value, nil)));
{
  open lseg2(first, last, final, v);
  switch (v) {
    case nil:
      close [f]lseg2(next, next, final, nil);
    case cons(head, tail):
      open node(first, ?firstNext, head); // To produce witness field.
      lseg2_add(firstNext);
      close [f]node(first, firstNext, head);
  }
  close [f]lseg2(first, next, final, append(v, cons(value, nil)));
}

lemma void lseg2_to_lseg(struct node *first)
  requires [?f]lseg2(first, ?last, ?final, ?v) &*& last == final;
  ensures [f]lseg(first, last, v);
{
  switch (v) {
    case nil:
      open lseg2(first, last, final, v);
      close [f]lseg(first, last, v);
    case cons(head, tail):
      open lseg2(first, last, final, v);
      open node(first, ?next, head);
      lseg2_to_lseg(next);
      close [f]node(first, next, head);
      close [f]lseg(first, last, v);
  }
}

@*/

int llist_length(struct llist *list)
  //@ requires [?frac]llist(list, ?_v);
  //@ ensures [frac]llist(list, _v) &*& result == length(_v);
{
  //@ open llist(list, _v);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ close [frac]lseg2(f, f, l, nil);
  while (n != l)
    //@ invariant [frac]lseg2(f, n, l, ?_ls1) &*& [frac]lseg(n, l, ?_ls2) &*& _v == append(_ls1, _ls2) &*& c + length(_ls2) == length(_v);
  {
    //@ open lseg(n, l, _ls2);
    //@ open node(n, _, _);
    struct node *next = n->next;
    //@ int value = n->value;
    //@ close [frac]node(n, next, n->value);
    //@ lseg2_add(f);
    n = next;
    if (c == 2147483647) abort();
    c = c + 1;
    //@ assert [frac]lseg(next, l, ?ls3);
    //@ append_assoc(_ls1, cons(value, nil), ls3);
  }
  //@ open lseg(n, l, _ls2);
  //@ append_nil(_ls1);
  //@ lseg2_to_lseg(f);
  //@ close [frac]llist(list, _v);
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?_v) &*& 0 <= index &*& index < length(_v);
  //@ ensures llist(list, _v) &*& result == nth(index, _v);
{
  //@ open llist(list, _);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ close lseg(f, n, nil);
  //@ drop_0(_v);
  while (i < index)
    //@ invariant 0 <= i &*& i <= index &*& lseg(f, n, ?_ls1) &*& lseg(n, l, ?_ls2) &*& _v == append(_ls1, _ls2) &*& _ls2 == drop(i, _v) &*& i + length(_ls2) == length(_v);
  {
    //@ length_drop(i, _v);
    //@ open lseg(n, l, _);
    //@ open node(n, _, _);
    //@ int value = n->value;
    struct node *next = n->next;
    //@ close node(n, next, n->value);
    //@ open lseg(next, l, ?ls3); // To produce a witness node for next.
    //@ lseg_add(n);
    //@ close lseg(next, l, ls3);
    //@ drop_n_plus_one(i, _v);
    n = next;
    i = i + 1;
    //@ append_assoc(_ls1, cons(value, nil), ls3);
  }
  //@ open lseg(n, l, _ls2);
  //@ open node(n, ?nnext, _);
  int value = n->value;
  //@ close lseg(n, l, _ls2);
  //@ lseg_append(f, n, l);
  //@ drop_n_plus_one(index, _v);
  return value;
}

int llist_removeFirst(struct llist *l)
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
  //@ assert lseg(nfn, nl, ?t);
  //@ close llist(l, t);
  return nfv;
}

void main0()
  //@ requires emp;
  //@ ensures emp;
{
  struct llist *l = create_llist();
  llist_add(l, 10);
  llist_add(l, 20);
  llist_add(l, 30);
  llist_add(l, 40);
  int x1 = llist_removeFirst(l);
  assert(x1 == 10);
  int x2 = llist_removeFirst(l);
  assert(x2 == 20);
  llist_dispose(l);
}

int main() //@ : main
  //@ requires emp;
  //@ ensures emp;
{
  struct llist *l1 = create_llist();
  struct llist *l2 = create_llist();
  llist_add(l1, 10);
  llist_add(l1, 20);
  llist_add(l1, 30);
  llist_add(l2, 40);
  llist_add(l2, 50);
  llist_add(l2, 60);
  int x = llist_removeFirst(l2); assert(x == 40);
  llist_append(l1, l2);
  int n = llist_length(l1); assert(n == 5);
  int e0 = llist_lookup(l1, 0); assert(e0 == 10);
  int e1 = llist_lookup(l1, 1); assert(e1 == 20);
  int e2 = llist_lookup(l1, 2); assert(e2 == 30);
  int e3 = llist_lookup(l1, 3); assert(e3 == 50);
  int e4 = llist_lookup(l1, 4); assert(e4 == 60);
  llist_dispose(l1);
  return 0;
}

struct iter {
    struct node *current;
};

/*@

predicate llist_with_node(struct llist *list, list<int> v0, struct node *n, list<int> vn) =
  list->first |-> ?f &*& list->last |-> ?l &*& malloc_block_llist(list) &*& lseg2(f, n, l, ?v1) &*& lseg(n, l, vn) &*& node(l, _, _) &*& v0 == append(v1, vn);

predicate iter(struct iter *i, real frac, struct llist *l, list<int> v0, list<int> v) =
  i->current |-> ?n &*& [frac]llist_with_node(l, v0, n, v) &*& malloc_block_iter(i);

@*/

struct iter *llist_create_iter(struct llist *l)
    //@ requires [?frac]llist(l, ?v);
    //@ ensures [frac/2]llist(l, v) &*& iter(result, frac/2, l, v, v);
{
    struct iter *i = 0;
    struct node *f = 0;
    //@ split_fraction llist(l, v) by 1/2;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    //@ open [frac/2]llist(l, v);
    f = l->first;
    i->current = f;
    //@ struct node *last = l->last;
    //@ close [frac/2]lseg2(f, f, last, nil);
    //@ close [frac/2]llist_with_node(l, v, f, v);
    //@ close iter(i, frac/2, l, v, v);
    return i;
}

int iter_next(struct iter *i)
    /*@
    requires
        iter(i, ?f, ?l, ?v0, ?v) &*&
        switch (v) {
            case nil: return false;
            case cons(h, t): return ensures result == h &*& iter(i, f, l, v0, t);
        };
    @*/
    //@ ensures emp;
{
    //@ open iter(i, f, l, v0, v);
    struct node *c = i->current;
    //@ open llist_with_node(l, v0, c, v);
    //@ open lseg(c, ?last, v);
    //@ open node(c, _, _);
    int value = c->value;
    struct node *n = c->next;
    //@ close [f]node(c, n, value);
    //@ assert [f]lseg2(?first, _, _, ?vleft);
    //@ lseg2_add(first);
    i->current = n;
    //@ assert [f]lseg(n, last, ?tail);
    //@ append_assoc(vleft, cons(value, nil), tail);
    //@ close [f]llist_with_node(l, v0, n, tail);
    //@ close iter(i, f, l, v0, tail);
    return value;
}

/*@

lemma void lseg2_lseg_append(struct node *n)
  requires [?frac]lseg2(?f, n, ?l, ?vs1) &*& [frac]lseg(n, l, ?vs2);
  ensures [frac]lseg(f, l, append(vs1, vs2));
{
  open lseg2(f, n, l, vs1);
  switch (vs1) {
    case nil:
    case cons(h, t):
      open [frac]node(f, ?next, h);
      lseg2_lseg_append(n);
      close [frac]node(f, next, h);
      close [frac]lseg(f, l, append(vs1, vs2));
  }
}

@*/

void iter_dispose(struct iter *i)
    //@ requires iter(i, ?f1, ?l, ?v0, ?v) &*& [?f2]llist(l, v0);
    //@ ensures [f1 + f2]llist(l, v0);
{
    //@ open iter(i, f1, l, v0, v);
    //@ open llist_with_node(l, v0, ?n, v);
    //@ lseg2_lseg_append(n);
    //@ close [f1]llist(l, v0);
    free(i);
}

int main2()
    //@ requires emp;
    //@ ensures emp;
{
    struct llist *l = create_llist();
    llist_add(l, 5);
    llist_add(l, 10);
    llist_add(l, 15);
    struct iter *i1 = llist_create_iter(l);
    struct iter *i2 = llist_create_iter(l);
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}
