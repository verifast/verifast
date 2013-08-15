#include "atomics.h"
#include "ticketlock_cap.h"

struct ticketlock {
  int next;
  int owner;
};

/*@
predicate range(int from, int to; list<int> vs) =
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
}

box_class ticketlock_box(struct ticketlock* l) {
  invariant l->next |-> ?next &*& l->owner |-> ?owner &*& owner <= next &*&
            0 <= owner &*&
            range(0, next, ?used) &*&
            ticketlock_box_next_dispenser(this, used) &*&
            malloc_block_ticketlock(l); 
  
  action noop();
    requires true;
    ensures owner == old_owner && next == old_next;
  
  action take(); // TAKE
    requires true;
    ensures owner == old_owner && next == old_next + 1;
  
  action permbased next(int ticket); // NEXT
    requires owner == ticket;
    ensures next == old_next && owner == old_owner + 1;
  
  handle_predicate holds_lock(int ticket) {
    invariant ticketlock_box_next(this, ticket) &*& owner == ticket &*& owner < next;
    
    preserved_by noop() { }
    
    preserved_by take() { }
    
    preserved_by next(action_ticket) {
      assert ticketlock_box_next(this, ticket) &*& [?f]ticketlock_box_next(this, action_ticket);
      if(ticket == action_ticket) {
        merge_fractions ticketlock_box_next(this, ticket); 
        action_permission1_unique(ticketlock_box_next, this, ticket);
      }
    }
  }
  
  handle_predicate is_ticket(int ticket) {
    invariant owner <= ticket &*& ticket < next &*& ticketlock_box_next(this, ticket);
    
    preserved_by noop() { }
    
    preserved_by take() { }
    
    preserved_by next(action_ticket) {
      assert action_ticket == old_owner;
      if(action_ticket == ticket) {
        merge_fractions ticketlock_box_next(this, ticket); 
        action_permission1_unique(ticketlock_box_next, this, ticket);
      }
    }
  }
}
@*/

//@ predicate ticketlock(struct ticketlock* l) = ticketlock_box(?id, l);
//@ predicate is_locked(struct ticketlock* l, real f) = [f]ticketlock_box(?id, l) &*& holds_lock(?h, id, _);

struct ticketlock* create_ticketlock()
  //@ requires true;
  //@ ensures result == 0 ? true : ticketlock(result);
{
  struct ticketlock* l = malloc(sizeof(struct ticketlock));
  if(l == 0) return 0;
  l->next = 0;
  l->owner = 0;
  //@ create_box id = ticketlock_box(l);
  //@ close ticketlock(l);
  return l;
}

void ticket_lock_lock(struct ticketlock* l)
  //@ requires [?f]ticketlock(l);
  //@ ensures is_locked(l, f);
{
  ;
  //@ open [f]ticketlock(l);
  //@ assert [f]ticketlock_box(?id, l);
  //@ handle h = create_handle ticketlock_box_handle(id);
  /*@
  consuming_box_predicate ticketlock_box(id, l)
  consuming_handle_predicate ticketlock_box_handle(h)
  perform_action take()
  { 
    
    assert l->next |-> ?n;
    assert l->owner |-> ?own;
    @*/
    int i = atomic_increment(&l->next);    
    /*@
    range_mem(0, i);
    close range(i, i + 1, cons(i, nil));
    range_append(0, i, i + 1);
    
    action_permission1_split2(ticketlock_box_next_dispenser, ticketlock_box_next, id, i);
    close ticketlock_next(l, n + 1);
  }
  producing_handle_predicate is_ticket(h, i);
  @*/
  while(true)
    //@ invariant [f]ticketlock_box(id, l) &*& is_ticket(h, id, i);
  {
    /*@
    consuming_box_predicate ticketlock_box(id, l)
    consuming_handle_predicate is_ticket(h, i)
    perform_action noop()
    { 
      @*/
      int o = atomic_load_int(&l->owner);
      /*@
    }
    producing_handle_predicate if(i == o) holds_lock(h, i) else is_ticket(h, i);
    @*/
    if(i == o) {
      //@ close is_locked(l, f);
      break; 
    }
  }
}

void ticket_lock_unlock(struct ticketlock* l)
  //@ requires is_locked(l, ?f);
  //@ ensures [f]ticketlock(l);
{
;
  //@ open is_locked(l, f);
  //@ assert holds_lock(?ha, ?id, ?ticket);
  /*@
  consuming_box_predicate ticketlock_box(id, l)
  consuming_handle_predicate holds_lock(ha, ticket)
  perform_action next(ticket)
  {
    @*/
    int i = atomic_increment(&l->owner);    
    /*@
    close ticketlock_owner(l, _);
  };
  @*/
  //@close [f]ticketlock(l);
  //@ leak ticketlock_box_next(id, _);
}