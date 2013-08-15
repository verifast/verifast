#include "atomic_integer.h"
#include "stdlib.h"

struct lock {
  int owner;
  //@ int owner_copy;
  int next;
  //@ int next_copy;
};

//@ predicate_ctor O(struct lock* l)(int value) = [1/2]l->owner_copy |-> value;
//@ predicate_ctor N(struct lock* l)(int value) = [1/2]l->next_copy |-> value;
//@ predicate lock(struct lock* l, predicate() I) = atomic_integer(&l->owner, ?level1, O(l)) &*& atomic_integer(&l->next, ?level2, N(l)) &*& tbox(?id, l, I) &*& malloc_block_lock(l) &*& level1 < box_level(id) &*& level2 < box_level(id);
//@ predicate locked(struct lock* l, predicate() I, real f) = [f]atomic_integer(&l->owner, ?level1, O(l)) &*& [f]atomic_integer(&l->next, ?level2, N(l)) &*& [f]tbox(?id, l, I) &*& [f]malloc_block_lock(l) &*& holds_lock(?ha, id, ?ticket) &*& level1 < box_level(id) &*& level2 < box_level(id);

/*@ predicate range(int from, int to; list<int> vs) =
  from >= to ?
    vs == nil
  :
    range(from + 1, to, ?nvs) &*& vs == cons(from, nvs);
    
lemma void range_append(int a, int b, int c)
  requires range(a, b, ?vs1) &*& range(b, c, ?vs2) &*& a <= b &*& b <= c;
  ensures range(a, c, append(vs1, vs2));
{
  open range(a, b, _);
  if(a >= b) {
  } else {
     range_append(a + 1, b, c);
  }
}

lemma void range_mem(int a, int b)
  requires range(a, b, ?vs);
  ensures range(a, b, vs) &*& ! mem(b, vs);
{
  open range(a, b, _);
  if(a >= b) {
  } else {
     range_mem(a + 1, b);
  }
}@*/

/*@
box_class tbox(struct lock* l, predicate() I) {
  invariant [1/2]l->owner_copy |-> ?owner &*& 0 <= owner &*& [1/2]l->next_copy |-> ?next &*& owner <= next &*& 
            range(0, next, ?used) &*& tbox_next_dispenser(this, used) &*& I();
  
  action take();
    requires true;
    ensures owner == old_owner && next == old_next + 1 && l == old_l;
    
  action permbased next(int ticket);
    requires owner == ticket;
    ensures owner == old_owner + 1 && next == old_next && l == old_l;
  
  action dummy();
    requires true;
    ensures owner == old_owner && next == old_next && l == old_l;
  
  handle_predicate is_ticket(int ticket) {
    invariant tbox_next(this, ticket) &*& owner <= ticket &*& ticket < next;
    
    preserved_by take() {
    }
    
    preserved_by next(action_ticket) {
      if(ticket == action_ticket) {
        merge_fractions tbox_next(this, ticket);
        action_permission1_unique(tbox_next, this, ticket);
      }
    }
    
    preserved_by dummy() {
    }
  }
  
  handle_predicate holds_lock(int ticket) {
    invariant tbox_next(this, ticket) &*& owner == ticket &*& owner < next;
    
    preserved_by take() {
    }
    
    preserved_by next(action_ticket) {
      merge_fractions tbox_next(this, ticket);
      action_permission1_unique(tbox_next, this, ticket);
    }
    
    preserved_by dummy() {
    }
  }
}
@*/

struct lock* create_lock()
  //@ requires exists<predicate()>(?I) &*& I();
  //@ ensures lock(result, I);
{
  struct lock* l = malloc(sizeof(struct lock));
  if(l == 0) abort();
  l->owner = 0;
  //@ l->owner_copy = 0;
  l->next = 0;
  //@ l->next_copy = 0;
  //@ close O(l)(0);
  //@ close N(l)(0);
  //@ create_atomic_integer(&l->owner, 1r, O(l));
  //@ create_atomic_integer(&l->next, 1r, N(l));
  //@ create_box id = tbox(l, I) above 1r;
  //@ close lock(l, I);
  return l;
}

void acquire(struct lock* l)
  //@ requires [?f]lock(l, ?I);
  //@ ensures locked(l, I, f);
{
  int i;
  //@ open [f]lock(l, I);
  //@ assert [f]tbox(?id, l, I);
  //@ assert [f]atomic_integer(&l->owner, ?level1, _) &*& [f]atomic_integer(&l->next, ?level2, _);
  {
    /*@
    predicate_family_instance atomic_integer_inc_pre(my_atomic_integer_inc_lemma)() = [f]tbox(id, l, I);
    predicate_family_instance atomic_integer_inc_post(my_atomic_integer_inc_lemma)(int old) = [f]tbox(id, l, I) &*& is_ticket(?ha, id, old);
    
    lemma void my_atomic_integer_inc_lemma()
      requires atomic_integer_inc_pre(my_atomic_integer_inc_lemma)() &*& N(l)(?value) &*& current_box_level(level2);
      ensures atomic_integer_inc_post(my_atomic_integer_inc_lemma)(value) &*& N(l)(value + 1) &*& current_box_level(level2);
    {
      open atomic_integer_inc_pre(my_atomic_integer_inc_lemma)();
      open N(l)(value);
      handle ha = create_handle tbox_handle(id);
      consuming_box_predicate tbox(id, l, I)
      consuming_handle_predicate tbox_handle(ha)
      perform_action take()
      {
        l->next_copy = l->next_copy + 1;
        range_mem(0, value);
        close range(value, value + 1, cons(value, nil));
        range_append(0, value, value + 1);
        action_permission1_split2(tbox_next_dispenser, tbox_next, id, value);
      }
      producing_handle_predicate is_ticket(ha, value);
      close N(l)(value + 1);
      close atomic_integer_inc_post(my_atomic_integer_inc_lemma)(value);
    }
    @*/
    //@ produce_lemma_function_pointer_chunk(my_atomic_integer_inc_lemma) : atomic_integer_inc_lemma(N(l), level2)() { call(); };
    //@ close atomic_integer_inc_pre(my_atomic_integer_inc_lemma)();
    i = atomic_integer_inc(&l->next);
    //@ open atomic_integer_inc_post(my_atomic_integer_inc_lemma)(_);
  }
  while(true)
    //@ invariant [f]tbox(id, l, I) &*& is_ticket(?ha, id, i) &*& [f]atomic_integer(&l->owner, level1, O(l));
  {
    /*@
    predicate_family_instance atomic_integer_get_pre(my_atomic_integer_get_lemma)() = [f]tbox(id, l, I) &*& is_ticket(ha, id, i);
    predicate_family_instance atomic_integer_get_post(my_atomic_integer_get_lemma)(int read) = [f]tbox(id, l, I) &*& read == i ? holds_lock(ha, id, i) : is_ticket(ha, id, i);
    
    lemma void my_atomic_integer_get_lemma()
      requires atomic_integer_get_pre(my_atomic_integer_get_lemma)() &*& O(l)(?value) &*& current_box_level(level1);
      ensures atomic_integer_get_post(my_atomic_integer_get_lemma)(value) &*& O(l)(value) &*& current_box_level(level1);
    {
      open atomic_integer_get_pre(my_atomic_integer_get_lemma)();
      open O(l)(value);
      consuming_box_predicate tbox(id, l, I)
      consuming_handle_predicate is_ticket(ha, i)
      perform_action dummy()
      {
      }
      producing_handle_predicate if(value == i) holds_lock(ha, i) else is_ticket(ha, i);
      close O(l)(value);
      close atomic_integer_get_post(my_atomic_integer_get_lemma)(value);
    }
    @*/
    //@ produce_lemma_function_pointer_chunk(my_atomic_integer_get_lemma) : atomic_integer_get_lemma(O(l), level1)() { call(); };
    //@ close atomic_integer_get_pre(my_atomic_integer_get_lemma)();
    int read = atomic_integer_get(&l->owner);
    //@ open atomic_integer_get_post(my_atomic_integer_get_lemma)(read);
    if(read == i) {
      break;
    }
  }
  //@ close locked(l, I, f);
}

void release(struct lock* l)
  //@ requires locked(l, ?I, ?f);
  //@ ensures [f]lock(l, I);
{
  //@ open locked(l, I, f);
  //@ assert holds_lock(?ha, ?id, ?i);
  //@ assert [f]atomic_integer(&l->owner, ?level1, _);
  {
    /*@
    predicate_family_instance atomic_integer_inc_pre(my_atomic_integer_inc_lemma)() = [f]tbox(id, l, I) &*& holds_lock(ha, id, i);
    predicate_family_instance atomic_integer_inc_post(my_atomic_integer_inc_lemma)(int old) = [f]tbox(id, l, I);
    
    lemma void my_atomic_integer_inc_lemma()
      requires atomic_integer_inc_pre(my_atomic_integer_inc_lemma)() &*& O(l)(?value) &*& current_box_level(level1);
      ensures atomic_integer_inc_post(my_atomic_integer_inc_lemma)(value) &*& O(l)(value + 1) &*& current_box_level(level1);
    {
      open atomic_integer_inc_pre(my_atomic_integer_inc_lemma)();
      open O(l)(value);
      consuming_box_predicate tbox(id, l, I)
      consuming_handle_predicate holds_lock(ha, i)
      perform_action next(i)
      {
        l->owner_copy = l->owner_copy + 1;
      };
      close O(l)(value + 1);
      close atomic_integer_inc_post(my_atomic_integer_inc_lemma)(value);
      leak tbox_next(_, _);
    }
    @*/
    //@ produce_lemma_function_pointer_chunk(my_atomic_integer_inc_lemma) : atomic_integer_inc_lemma(O(l), level1)() { call(); };
    //@ close atomic_integer_inc_pre(my_atomic_integer_inc_lemma)();
    int old = atomic_integer_inc(&l->owner);
    //@ open atomic_integer_inc_post(my_atomic_integer_inc_lemma)(_);
  }
  //@ close [f]lock(l, I);
}


