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
  
  action noop();
    requires true;
    ensures l == old_l && I == old_I && locked == old_locked;
  
  action acquire();
    requires true;
    ensures l == old_l && (old_locked == 0 ? locked != 0 : locked == old_locked);
  
  action release();
    requires locked != 0;
    ensures l == old_l && locked == 0;
  
  handle_predicate holds_lock() {
    invariant [1/2]integer(l, locked) &*& locked != 0;
    
    preserved_by noop() {
    }
    
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
  //@ requires int_(l, _) &*& exists<predicate()>(?I);
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
    //@ invariant [f/2]gbox(id, l, I) &*& gbox_handle(ha, id);
  {
    /*@
    consuming_box_predicate gbox(id, l, I)
    consuming_handle_predicate gbox_handle(ha)
    perform_action  acquire()
    { 
      @*/ int read = atomic_compare_and_set_int(l, 0, 1); /*@ 
    }
    producing_handle_predicate if (read == 0) holds_lock(ha) else gbox_handle(ha);
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
    perform_action  release()
    { 
      @*/ atomic_set_int(l, 0); /*@ 
    };
    @*/
}

/*@
box_class b() {
  invariant true;
  
  action noop();
    requires true;
    ensures true;
}
@*/

void finalize(int* l)
  //@ requires lock(l, ?I) &*& locked(l, I);
  //@ ensures integer(l, _);
{
  //@ open lock(l, I);
  //@ open locked(l, I);
  //@ assert [_]gbox(?id1, l, I) &*& [_]gbox(?id2, l, I) &*& holds_lock(?ha, id1);
  //@ create_box id0 = b() below box_level(id1), box_level(id2); 
  ;
  /*@
    consuming_box_predicate b(id0) 
    perform_action noop()
    {
      if(id1 != id2) {
        box_level_unique(id1, id2);
        if(box_level(id1) < box_level(id2)) {
          consuming_box_predicate gbox(id1, l, I)
          consuming_handle_predicate holds_lock(ha)
          perform_action noop()
          {
            consuming_box_predicate gbox(id2, l, I)
            perform_action noop()
             {
              integer_unique(l);
            };
          };
        } else {
          consuming_box_predicate gbox(id2, l, I)
          perform_action noop()
          {
            consuming_box_predicate gbox(id1, l, I)
            consuming_handle_predicate holds_lock(ha)
            perform_action noop()
            {
              integer_unique(l);
            };
          };
        } 
      }
    };
  @*/
  //@ dispose_box gbox(id1, l, I) and_handle holds_lock(_);
  //@ dispose_box b(id0);
}

 void merge_locks(int* l)
  //@ requires [?f1]lock(l, ?I) &*& [?f2]lock(l, I) &*& locked(l, I);
  //@ ensures [f1 + f2]lock(l, I) &*& locked(l, I);
{
  //@ open [f1]lock(l, I);
  //@ open [f2]lock(l , I);
  //@ open locked(l, I);
  //@ assert [f1/2]gbox(?id1, l, I) &*& [f2/2]gbox(?id2, l, I) &*& [1/2]gbox(?id3, l, I);
 //@ create_box id0 = b() below box_level(id1), box_level(id2), box_level(id3); 
  ;
  /*@  consuming_box_predicate b(id0) 
    perform_action noop()
    {
      if(id1 != id3) {
        box_level_unique(id1, id3);
        if(box_level(id1) < box_level(id3)) {
          consuming_box_predicate gbox(id1, l, I)
          perform_action noop()
          {
            consuming_box_predicate gbox(id3, l, I)
            consuming_handle_predicate holds_lock(_)
            perform_action noop()
             {
              integer_unique(l);
            };
          };
        } else {
          consuming_box_predicate gbox(id3, l, I)
          consuming_handle_predicate holds_lock(_)
          perform_action noop()
          {
            consuming_box_predicate gbox(id1, l, I)
            
            perform_action noop()
            {
              integer_unique(l);
            };
          };
        } 
      }
   };@*/
   /*@  consuming_box_predicate b(id0) 
    perform_action noop()
    {
      if(id2 != id3) {
        box_level_unique(id2, id3);
        if(box_level(id2) < box_level(id3)) {
          consuming_box_predicate gbox(id2, l, I)
          perform_action noop()
          {
            consuming_box_predicate gbox(id3, l, I)
            consuming_handle_predicate holds_lock(_)
            perform_action noop()
             {
              integer_unique(l);
            };
          };
        } else {
          consuming_box_predicate gbox(id3, l, I)
          consuming_handle_predicate holds_lock(_)
          perform_action noop()
          {
            consuming_box_predicate gbox(id2, l, I)
            
            perform_action noop()
            {
              integer_unique(l);
            };
          };
        } 
      }
   };@*/
  //@ assert id1 == id3;
  //@ close locked(l, I);
  //@ merge_fractions gbox(id1, _, _);
  //@ close [f1 + f2]lock(l, I);
  //@ dispose_box b(id0);
}

