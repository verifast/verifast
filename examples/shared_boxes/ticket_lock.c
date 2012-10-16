#include "atomics.h"
#include "ticket_lock.h"

struct ticket_lock {
  int next;
  int owner;
  //@ real acquiringFrac;
  //@ int help;
};

/*@
box_class ticket_lock_box(struct ticket_lock* l, predicate() I) {
  invariant l->next |-> ?next &*& l->owner |-> ?owner &*& l->acquiringFrac |-> ?acquiringFrac &*& 
            exists<list<handle> >(?thandles) &*&
            owner <= next &*&
            (next == owner ? acquiringFrac == 0 : true) &*&
            (acquiringFrac > 0 ? owner < next &*& [acquiringFrac]l->help |-> _ : I() &*& acquiringFrac == 0) &*& 
            length (thandles) == next - owner &*&
            malloc_block_ticket_lock(l); 
  
  action get_ticket();
    requires true;
    ensures owner == old_owner && next == old_next + 1 && acquiringFrac == old_acquiringFrac && thandles == append(old_thandles, cons(actionHandle, nil));
  
  action acquire(int ticket, real f);
    requires owner <= ticket && 0 < f;
    ensures next == old_next && owner == old_owner && (old_owner == ticket && actionHandle == head(thandles) ? old_acquiringFrac == 0 && acquiringFrac == f : acquiringFrac == old_acquiringFrac) && thandles == old_thandles; 
    
  action release(int ticket);
    requires acquiringFrac != 0 && owner == ticket && head(thandles) == actionHandle;
    ensures owner == old_owner + 1 && next == old_next && acquiringFrac == 0 && thandles == tail(old_thandles);
  
  handle_predicate is_ticket(int ticket, bool holdsLock, real f) {
    invariant holdsLock ?
                owner == ticket && acquiringFrac > 0 && head(thandles) == predicateHandle && acquiringFrac == f
              :
                owner <= ticket && ticket < next && nth(ticket - owner, thandles) == predicateHandle &&
                (acquiringFrac > 0 ? owner < ticket : true) &&
                length(thandles) >= ticket - owner + 1;
        
    preserved_by get_ticket() {
      switch(old_thandles) {
        case nil:
        case cons(h, t):
      }
     nth_append(old_thandles, cons(actionHandle, nil), ticket - owner);
    }
    
    preserved_by acquire(action_ticket, action_f) {
      switch(thandles) {
        case nil:
        case cons(h, t):
      }
    }
    
    preserved_by release(action_ticket) {
      switch(thandles) {
        case nil:
        case cons(h, t):
      }
      switch(old_thandles) {
        case nil:
        case cons(h, t):
      }
    }
  }
}
@*/

//@ predicate ticket_lock(struct ticket_lock* l, predicate() I) = ticket_lock_box(?id, l, I) &*& l->help |-> _;
//@ predicate is_locked(struct ticket_lock* l, real f, predicate() I) = [f]ticket_lock_box(?id, l, I) &*& is_ticket(?h, id, _, true, f);

struct ticket_lock* create_ticket_lock()
  //@ requires exists<predicate()>(?I) &*& I();
  //@ ensures result == 0 ? I() : ticket_lock(result, I);
{
  struct ticket_lock* l = malloc(sizeof(struct ticket_lock));
  if(l == 0) return 0;
  l->next = 0;
  l->owner = 0;
  //@ l->acquiringFrac = 0;
  //@ close exists(nil);
  //@ close exists(0r);
  //@ create_box id = ticket_lock_box(l, I);
  //@ close ticket_lock(l, I);
  return l;
}

void ticket_lock_lock(struct ticket_lock* l)
  //@ requires [?f]ticket_lock(l, ?I);
  //@ ensures is_locked(l, f, I) &*& I();
{
  ;
  //@ open [f]ticket_lock(l, I);
  //@ assert [f]ticket_lock_box(?id, l, I);
  //@ handle h = create_handle ticket_lock_box_handle(id);
  /*@
  consuming_box_predicate ticket_lock_box(id, l, I)
  consuming_handle_predicate ticket_lock_box_handle(h)
  perform_action get_ticket() atomic
  { 
    assert l->next |-> ?n;
    assert l->owner |-> ?own;
    @*/
    int i = atomic_increment(&l->next);    
    /*@
    close ticket_lock_next(l, n + 1);
    open exists(?thandles);
    close exists(append(thandles, cons(h, nil)));
    assert length(thandles) == n - own;
    nth_append_r(thandles, cons(h, nil), 0); 
  }
  producing_handle_predicate is_ticket(i, false, 0);
  @*/
  while(true)
    //@ invariant [f]ticket_lock_box(id, l, I) &*& [f]l->help |-> _ &*& is_ticket(h, id, i, false, _);
  {
    /*@
    consuming_box_predicate ticket_lock_box(id, l, I)
    consuming_handle_predicate is_ticket(h, i, false, _)
    perform_action acquire(i, f) atomic
    { 
      assert l->acquiringFrac |-> ?myf;
      assert exists<list<handle> >(?hndls);
      switch(hndls) {
        case nil:
        case cons(h_, t_):
      }
      @*/
      int o = atomic_load_int(&l->owner);
      /*@
      if(i == o) { 
        l->acquiringFrac = f;
      }
    }
    producing_handle_predicate is_ticket(i, i == o, i == o ? f : myf);
    @*/
    if(i == o) {
      //@ close is_locked(l, f, I);
      break; 
    }
  }
}

void ticket_lock_unlock(struct ticket_lock* l)
  //@ requires is_locked(l, ?f, ?I) &*& I();
  //@ ensures [f]ticket_lock(l, I);
{
;
  //@ open is_locked(l, f, I);
  //@ assert is_ticket(?h, ?id, ?ticket, true, f);
  /*@
  consuming_box_predicate ticket_lock_box(id, l, I)
  consuming_handle_predicate is_ticket(h, ticket, true, f)
  perform_action release(ticket) atomic
  {
    @*/
    int i = atomic_increment(&l->owner);    
    /*@
    close ticket_lock_owner(l, _);
    open exists<list<handle> >(?thandles); close exists(tail(thandles));
    switch(thandles) {
      case nil:
      case cons(h_, t_):
    }
    l->acquiringFrac = 0;
  }
  producing_handle_predicate ticket_lock_box_handle();
  @*/
  //@ close [f]ticket_lock(l, I);
  //@ leak ticket_lock_box_handle(_, _);
}

void ticket_lock_dispose(struct ticket_lock* l)
  //@ requires ticket_lock(l, ?I);
  //@ ensures I();
{
  //@ open ticket_lock(l, I);
  //@ assert ticket_lock_box(?id, l, I);
  //@ dispose_box ticket_lock_box(id, l, I);
  free(l);
  //@ open exists(_);
}
