#include "gotsmanlock.h"
#include "atomics.h"

/*
Options for verifying finalize:
1) Make acquire permbased. Finalize has full permission to acquire + nobody else can release, so safe to destroy the box.
2) Use fractional permissions (cfr Dominique) and implement split, merge and dispose actions (precondition of dispose: alive_handle(1r)).
3) See below.
*/

/*@
box_class gbox(int* l, predicate() I)
{
  invariant [1/2]integer(l, ?locked) &*& locked == 0 ? I() &*& [1/2]integer(l, 0) &*& [1/2]gbox(this, l, I) : true;
  
  action acquire();
    requires true;
    ensures l == old_l && (old_locked == 0 ? locked != 0 : locked == old_locked);
    
  action release();
    requires locked != 0;
    ensures l == old_l && locked == 0;
  
  handle_predicate holds_lock() {
    invariant [1/2]integer(l, locked) &*& locked != 0;
    
    preserved_by acquire() {
    }
    
    preserved_by release() {
      merge_fractions integer(l, _);
      integer_unique(l);
    }
  }
}
@*/

/*@
predicate lock(int* l, predicate() I) = [1/2]gbox(?id, l, I);
predicate locked(int* l, predicate() I) = [1/2]gbox(?id, l, I) &*& holds_lock(?ha, id);
@*/

void init(int* l)
  //@ requires integer(l, _) &*& exists<predicate()>(?I);
  //@ ensures lock(l, I) &*& locked(l, I);
{
  *l = 1;
  //@ create_box id = gbox(l, I) and_handle ha = holds_lock();
  //@ close lock(l, I);
  //@ close locked(l, I);
}

void acquire(int* l)
  //@ requires [?f]lock(l, ?I);
  //@ ensures [f]lock(l, I) &*& locked(l, I) &*& I();
{
  //@ open [f]lock(l, I);
  //@ assert [_]gbox(?id, l, I);
  //@ handle ha = create_handle gbox_handle(id);
  while(true)
    //@ invariant [f/2]gbox(id, l, I) &*& gbox_handle(ha, id);//&*& [f]gbox_acquire(id);
  {
    /*@
    consuming_box_predicate gbox(id, l, I)
    consuming_handle_predicate gbox_handle(ha)
    perform_action  acquire() atomic
    { 
      @*/ int read = atomic_compare_and_set_int(l, 0, 1); /*@ 
    }
    producing_handle_predicate if (read == 0) holds_lock() else gbox_handle();
    @*/  
    if(read == 0) {
      //@ close locked(l, I);
      //@ close [f]lock(l, I);
      break;
    }
  }
}

void release(int* l)
  //@ requires locked(l, ?I) &*& I();
  //@ ensures true;
{
  ;
  //@ open locked(l, I);
  //@ assert [_]gbox(?id, l, I) &*& holds_lock(?ha, id);
  /*@
    consuming_box_predicate gbox(id, l, I)
    consuming_handle_predicate holds_lock(ha)
    perform_action  release() atomic
    { 
      @*/ atomic_set_int(l, 0); /*@ 
    }
    producing_handle_predicate gbox_handle();
    @*/
    //@ leak gbox_handle(ha, id);
}

void finalize(int* l)
  //@ requires lock(l, ?I) &*& locked(l, I);
  //@ ensures integer(l, _);
{
  //@ open lock(l, I);
  //@ open locked(l, I);
  //@ assert [_]gbox(?id, l, I) &*& [_]gbox(?id2, l, I);
  //@ assume(id == id2); // use some ghost state to prove this, shouldn't be hard
  //@ dispose_box gbox(id, l, I) and_handle holds_lock(_);
}
