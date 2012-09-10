#include "atomics.h"
#include "simplelock.h"

struct lock {
  int is_locked;
  //@ int helper;
};

/*@
box_class lock_box(struct lock* l, handle owner, real myf, predicate() I)
{
  invariant l->is_locked |-> ?is_locked &*& malloc_block_lock(l) &*& is_locked == 0 ? I() : [myf]l->helper |-> _;
  
  action acquire(real f);
    requires true;
    ensures old_is_locked == 0 ? is_locked == 1 && owner == actionHandle && myf == f: is_locked == old_is_locked && owner == old_owner && myf == old_myf;
  
  action release();
    requires is_locked == 1 && owner == actionHandle;
    ensures is_locked == 0;
    
  handle_predicate default_handle() {
    invariant true;
    
    preserved_by acquire(f0) {}
    preserved_by release() {}
  }
    
  handle_predicate locked_handle(bool success) {
    invariant success ? is_locked == 1 && owner == predicateHandle : true;
    
    preserved_by acquire(f0) {
    }
    preserved_by release() {
    }
  }
}

predicate is_lock(struct lock* l, predicate() I) =
  lock_box(?id, l, _, _, I) &*& l->helper |-> _;
  
predicate locked(struct lock* l, predicate() I, real f) =
  [f]lock_box(?id, l, ?ha, f, I) &*& locked_handle(ha, id, true);
@*/

struct lock* create_lock()
  //@ requires exists<predicate()>(?I) &*& I();
  //@ ensures result == 0 ? I() : is_lock(result, I);
{
  //@ open exists(I);
  struct lock* l = malloc(sizeof(struct lock));
  if(l == 0) return 0;
  l->is_locked = 0;
  //@ create_box id = lock_box(l, ha, 0, I) and_handle ha = default_handle();
  //@ leak default_handle(ha, id);
  //@ close is_lock(l, I); 
  return l;
}

void lock_acquire(struct lock* l)
  //@ requires [?f]is_lock(l, ?I);
  //@ ensures locked(l, I, f) &*& I();
{
  while(true)
    //@ invariant [f]is_lock(l, I);
  {
    //@ open [f]is_lock(l, I);
    //@ assert [f]lock_box(?id, l, ?owner, ?myf, I);
    //@ handle ha = create_handle lock_box_handle(id);
    /*@
    consuming_box_predicate lock_box(id, l, owner, myf, I)
    consuming_handle_predicate lock_box_handle(ha)
    perform_action acquire(f) atomic
    {
      @*/ int old = atomic_compare_and_set_int(&l->is_locked, 0, 1); /*@
      if(old == 0) {
      } else {
      }
    }
    producing_box_predicate lock_box(l, old == 0 ? ha : owner, old == 0 ? f : myf, I)
    producing_handle_predicate locked_handle(old == 0);
    @*/
    if(old == 0) {
      //@ close locked(l, I, f);
      break;
    } else {
      //@ close [f]is_lock(l, I);
      //@ leak locked_handle(ha, id, false);
    }
  }
}

void lock_release(struct lock* l)
  //@ requires locked(l, ?I, ?f) &*& I();
  //@ ensures [f]is_lock(l, I);
{
  ;
  //@ open locked(l, I, f);
  //@ assert [f]lock_box(?id, l, ?owner, ?myf, I);
  //@ assert locked_handle(owner, id, true);
  /*@
    consuming_box_predicate lock_box(id, l, owner, myf, I)
    consuming_handle_predicate locked_handle(owner, true)
    perform_action release() atomic
    {
      @*/ atomic_set_int(&l->is_locked, 0); /*@
    }
    producing_handle_predicate default_handle();
    @*/
    //@ close [f]is_lock(l, I);
    //@ leak default_handle(owner, _);
}

void lock_dispose(struct lock* l)
  //@ requires is_lock(l, ?I);
  //@ ensures I();
{
  //@ open is_lock(l, I);
  //@ dispose_box lock_box(_, l, _, _, I);
  free(l);
}

  

