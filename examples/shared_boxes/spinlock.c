#include "atomics.h"
#include "spinlock.h"
#include <stdbool.h>
#include "malloc.h"

struct spinlock {
  int is_locked;
  //@ int helper;
};

/*@
box_class spinlock_box(struct spinlock* l, predicate() I)
{
  invariant l->is_locked |-> ?is_locked &*& exists<handle>(?owner) &*& exists<real>(?myf) &*& malloc_block_spinlock(l) &*& 
            is_locked == 0 ? I() : [myf]l->helper |-> _;
  
  action noop();
    requires true;
    ensures is_locked == old_is_locked && owner == old_owner && myf == old_myf;
  
  action acquire(real f);
    requires true;
    ensures old_is_locked == 0 ? is_locked == 1 && cons(owner, nil) == actionHandles && myf == f: is_locked == old_is_locked && owner == old_owner && myf == old_myf;
  
  action release();
    requires is_locked == 1 && cons(owner, nil) == actionHandles;
    ensures is_locked == 0;
    
  handle_predicate locked_handle(real f) {
    invariant is_locked == 1 && owner == predicateHandle && myf == f;
    
    preserved_by noop() { }
    preserved_by acquire(f0) { }
    preserved_by release() { }

  }
}

predicate spinlock(struct spinlock* l, predicate() I) =
  spinlock_box(?id, l, I) &*& l->helper |-> _;
  
predicate locked(struct spinlock* l, predicate() I, real f) =
  [f]spinlock_box(?id, l, I) &*& locked_handle(?ha, id, f);
@*/

struct spinlock* create_spinlock()
  //@ requires exists<predicate()>(?I) &*& I();
  //@ ensures result == 0 ? I() : spinlock(result, I);
{
  //@ open exists(I);
  struct spinlock* l = malloc(sizeof(struct spinlock));
  if(l == 0) return 0;
  l->is_locked = 0;
  //@ handle ha0;
  //@ close exists<handle>(ha0);
  //@ close exists<real>(0);
  //@ create_box id = spinlock_box(l, I);
  //@ close spinlock(l, I); 
  return l;
}

void spinlock_acquire(struct spinlock* l)
  //@ requires [?f]spinlock(l, ?I);
  //@ ensures locked(l, I, f) &*& I();
{
  //@ open [f]spinlock(l, I);
  //@ assert [f]spinlock_box(?id, l, I);
  //@ handle ha = create_handle spinlock_box_handle(id);
  while(true)
    //@ invariant [f]spinlock_box(id, l, I) &*& [f]l->helper |-> _ &*& spinlock_box_handle(ha, id);
  {
    /*@
    consuming_box_predicate spinlock_box(id, l, I)
    consuming_handle_predicate spinlock_box_handle(ha)
    perform_action acquire(f)
    {
      @*/ int old = atomic_compare_and_set_int(&l->is_locked, 0, 1); /*@
      if(old == 0) {
        open exists<real>(_); close exists<real>(f);
        open exists<handle>(_); close exists<handle>(ha);       
      }
    }
    producing_handle_predicate if (old != 0) spinlock_box_handle(ha) else locked_handle(ha, f);
    @*/
    if(old == 0) {
      //@ close locked(l, I, f);
      break;
    }
  }
}

void spinlock_release(struct spinlock* l)
  //@ requires locked(l, ?I, ?f) &*& I();
  //@ ensures [f]spinlock(l, I);
{
  ;
  //@ open locked(l, I, f);
  //@ assert [f]spinlock_box(?id, l, I);
  //@ assert locked_handle(?owner, id, f);
  /*@
  consuming_box_predicate spinlock_box(id, l, I)
  consuming_handle_predicate locked_handle(owner, f)
  perform_action release()
  {
    @*/ atomic_set_int(&l->is_locked, 0); /*@
  };
  @*/
  //@ close [f]spinlock(l, I);
}

void spinlock_dispose(struct spinlock* l)
  //@ requires spinlock(l, ?I);
  //@ ensures I();
{
  //@ open spinlock(l, I);
  //@ dispose_box spinlock_box(_, l, I);
  free(l);
  //@ open exists(_);
  //@ open exists(_);
}

/*@
lemma void change_invariant(struct spinlock* l, predicate() J)
  requires spinlock(l, ?I) &*& J();
  ensures spinlock(l, J) &*& I();
{
  open spinlock(l, I);
  assert spinlock_box(?id, l, I);
  handle ha = create_handle spinlock_box_handle(id);
  consuming_box_predicate spinlock_box(id, l, I)
  consuming_handle_predicate spinlock_box_handle(ha)
  perform_action noop()
  {
  }
  producing_box_predicate spinlock_box(l, J);
  close spinlock(l, J);
}
@*/

