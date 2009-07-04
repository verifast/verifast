#ifndef LISTS_H
#define LISTS_H

struct list;
struct iter;

/*@
inductive list<t> = nil | cons(t, list<t>);

fixpoint list<t> add<t>(list<t> v, t e)
{
  switch(v) {
    case nil: return cons(e, nil);
    case cons(h, t): return cons(h, add(t, e));
  }
}

fixpoint list<t> remove<t>(list<t> v, t e)
{
  switch(v) {
    case nil: return nil;
    case cons(h, t): return h==e?t:cons(h, remove(t, e));
  }
}

fixpoint int length<t>(list<t> v)
{
  switch(v) {
    case nil: return 0;
    case cons(h, t): return 1 + length(t);
  }
}

fixpoint t head<t>(list<t> v)
{
  switch(v) {
    case nil: return default<t>;
    case cons(h, t): return h;
  }
}

fixpoint list<t> tail<t>(list<t> v)
{
  switch(v) {
    case nil: return nil;
    case cons(h, t): return t;
  }
}

fixpoint t ith<t>(list<t> v, int i)
{
  switch(v) {
    case nil: return default<t>;
    case cons(h, t): return i==0 ? h : ith(t, i - 1);
  }
}

fixpoint bool contains<t>(list<t> v, t x)
{
  switch(v) {
    case nil: return false;
    case cons(h, t): return h==x ? true : contains(t, x);
  }
}

fixpoint bool uniqueElements<t>(list<t> v)
{
  switch(v) {
    case nil: return true;
    case cons(h, t): return !contains(t, h) && uniqueElements(t);
  }
}

lemma void lengthPositive<t>(list<t> v)
  requires true;
  ensures 0<=length(v);
{
  switch(v){
    case nil: return;
    case cons(h, t): lengthPositive(t);
  }
}

lemma void containsIth<t>(list<t> v, int i)
  requires 0<=i &*& i < length(v);
  ensures contains(v, ith(v, i)) == true;
{
  switch(v){
    case nil: return;
    case cons(h, t):
      if(i==0){
      } else {
        containsIth(t, i - 1);
      }
  }
}

predicate foreach<t>(list<t> v, predicate(t) p)
  requires uniqueElements(v)==true &*& switch(v) { 
             case nil: return emp; 
             case cons(h, t): return p(h) &*& foreach(t, p);
           }; 

lemma void removeContains<t>(list<t> v, t x1, t x2)
    requires !contains(v, x1);
    ensures  !contains(remove(v, x2), x1);
{
    switch (v) {
        case nil:
        case cons(h, t):
            if (h == x2) {
            } else {
                removeContains(t, x1, x2);
            }
    }
}

lemma void removeUniqueElements<t>(list<t> v, t x)
    requires uniqueElements(v) == true;
    ensures uniqueElements(remove(v, x)) == true;
{
    switch (v) {
        case nil:
        case cons(h, t):
            if (h == x) {
            } else {
                removeContains(t, h, x);
                removeUniqueElements(t, x);
            }
    }
}

lemma void remove_not_contains<t>(list<t> v, t mem)
  requires !contains(v, mem);
  ensures remove(v, mem) == v;
{
  switch (v) {
    case nil:
    case cons(h, t):
      if (h == mem) {
      } else {
      }
      remove_not_contains(t, mem);
  }
}

lemma void foreach_unremove<t>(list<t> v, t x)
  requires foreach(remove(v, x), ?p) &*& contains(v, x)==true &*& p(x) &*& uniqueElements(v) == true;
  ensures foreach(v, p);
{
  switch(v) {
    case nil: open foreach<t>(remove(v, x), p); return;
    case cons(h, t):
      if(h==x){
        remove_not_contains(t, x);
        close foreach<t>(v, p);
      } else {
        open foreach<t>(remove(v, x), p);
        assert remove(v, x) == cons(h, remove(t, x));
        foreach_unremove(t, x);
        close foreach<t>(v, p);
      }
  }
}

lemma void foreach_remove<t>(list<t> v, t x)
    requires foreach<t>(v, ?p) &*& contains(v, x) == true;
    ensures foreach<t>(remove(v, x), p) &*& p(x) &*& uniqueElements(v) == true;
{
    switch (v) {
        case nil:
        case cons(h, t):
            open foreach<t>(v, p);
            if (h == x) {
            } else {
                foreach_remove(t, x);
                removeUniqueElements(v, x);
                close foreach<t>(remove(v, x), p);
            }
    }
}

@*/

/*@

predicate list(struct list* l, list<void *> v);

predicate iter(struct iter* i, struct list* l, list<void *> v, int index);

@*/

struct list *create_list();
  //@ requires emp;
  //@ ensures list(result, nil);
int list_length(struct list* list);
  //@ requires list(list, ?v);
  //@ ensures list(list, v) &*& result == length(v);
void* list_removeFirst(struct list* list);
  //@ requires list(list, ?v);
  //@ ensures list(list, tail(v)) &*& result == head(v);
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

#endif