#include "atomics.h"

struct spinlock {
  int locked;
  //@ real helper;
};

/*@
box_class spinlock_box(struct spinlock* s, predicate() I) {
  invariant s->locked |-> ?locked &*& exists<real>(?myf) &*& locked == 0 ? spinlock_box_release(this) &*& I() : [myf]s->helper |-> _ &*& locked == 1;   
  
  action acquire(real f);
    requires true;
    ensures s == old_s && I == old_I && (old_locked == 0 ? myf == f && locked == 1 : myf == old_myf && locked == old_locked);
   
  action permbased release();
    requires locked == 1;
    ensures s == old_s && I == old_I && locked == 0;
    
  handle_predicate is_locked(real f) {
    invariant spinlock_box_release(this) &*& locked == 1 && myf == f;
    
    preserved_by acquire(f2) {
    }
    
    preserved_by release() {
      merge_fractions spinlock_box_release(this);
      action_permission0_unique(spinlock_box_release, this);
    }
  }
}

predicate spinlock(struct spinlock* l, predicate() I) =
  spinlock_box(?id, l, I) &*& malloc_block_spinlock(l) &*& l->helper |-> _;
  
predicate locked(struct spinlock* l, predicate() I, real f) =
  [f]spinlock_box(?id, l, I) &*& [f]malloc_block_spinlock(l) &*& is_locked(?ha, id, f);
@*/

struct spinlock* create_spinlock()
  //@ requires exists<predicate()>(?I) &*& I();
  //@ ensures result == 0 ? I() : spinlock(result, I);
{
  //@ open exists(I);
  struct spinlock* l = malloc(sizeof(struct spinlock));
  if(l == 0) return 0;
  l->locked = 0;
  //@ handle ha0;
  //@ close exists<real>(0r);
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
    //@ invariant [f]spinlock_box(id, l, I) &*& spinlock_box_handle(ha, id) &*& [f]malloc_block_spinlock(l) &*& [f]l->helper |-> _;
  {
    /*@
    consuming_box_predicate spinlock_box(id, l, I)
    consuming_handle_predicate spinlock_box_handle(ha)
    perform_action acquire(f) atomic
    {
      @*/ int old = atomic_compare_and_set_int(&l->locked, 0, 1); /*@
      if(old == 0) {
        open exists(_);
        close exists(f);
      }
    }
    producing_handle_predicate if (old != 0) spinlock_box_handle() else is_locked(f);
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
{ ;
  //@ open locked(l, I, f);
  //@ assert [f]spinlock_box(?id, l, I);
  //@ assert is_locked(?owner, id, f);
  /*@
  consuming_box_predicate spinlock_box(id, l, I)
  consuming_handle_predicate is_locked(owner, f)
  perform_action release() atomic
  {
    @*/ atomic_set_int(&l->locked, 0); /*@
  }
  producing_handle_predicate spinlock_box_handle();
  @*/
  //@ close [f]spinlock(l, I);
  //@ leak spinlock_box_handle(_, _);
}