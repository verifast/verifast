struct list;
struct iter;

/*@
inductive listval = | nil | cons(void*, listval);

fixpoint listval add(listval v, void* e)
{
  switch(v) {
    case nil: return cons(e, nil);
    case cons(h, t): return cons(h, add(t, e));
  }
}

fixpoint listval remove(listval v, void* e)
{
  switch(v) {
    case nil: return nil;
    case cons(h, t): return h==e?t:cons(h, remove(t, e));
  }
}

fixpoint int length(listval v)
{
  switch(v) {
    case nil: return 0;
    case cons(h, t): return 1 + length(t);
  }
}

fixpoint listval tail(listval v)
{
  switch(v) {
    case nil: return nil;
    case cons(h, t): return t;
  }
}

fixpoint void* ith(listval v, int i)
{
  switch(v) {
    case nil: return 0;
    case cons(h, t): return i==0 ? h : ith(t, i - 1);
  }
}


fixpoint bool contains(listval v, void* x)
{
  switch(v) {
    case nil: return false;
    case cons(h, t): return h==x ? true : contains(t, x);
  }
}

fixpoint bool uniqueElements(listval v)
{
  switch(v) {
    case nil: return true;
    case cons(h, t): return !contains(t, h) && uniqueElements(t);
  }
}

lemma void lengthPositive(listval v);
  requires true;
  ensures 0<=length(v);

lemma void containsIth(listval v, int i);
  requires 0<=i && i < length(v);
  ensures contains(v, ith(v, i)) == true;

predicate list(struct list* l, listval v);

predicate iter(struct iter* i, struct list* l, listval v, int index);
@*/

struct list *create_list();
  //@ requires emp;
  //@ ensures list(result, nil);
struct iter *list_create_iter(struct list *list);
  //@ requires list(list, ?v);
  //@ ensures iter(result, list, v, 0);
bool iter_has_next(struct iter *iter);
  //@ requires iter(iter, ?l, ?v, ?i);
  //@ ensures iter(iter, l, v, i) &*& result == (i < length(v));   
void *iter_next(struct iter *iter);
  //@ requires iter(iter, ?l, ?v, ?i) &*& i < length(v);
  //@ ensures iter(iter, l, v, i + 1) &*& result==ith(v, i);
void iter_dispose(struct iter *iter);
  //@ requires iter(iter, ?l, ?v, ?i);
  //@ ensures list(l, v);
void list_add(struct list *list, void *element);
  //@ requires list(list, ?v);
  //@ ensures list(list, cons(element, v));
void list_remove(struct list *list, void *element);
  //@ requires list(list, ?v) &*& contains(v, element) == true;
  //@ ensures list(list, remove(v, element));
void list_dispose(struct list *list);
  //@ requires list(list, ?v);
  //@ ensures emp;
