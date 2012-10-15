#include "threading.h"
#include "atomics.h"

/*@
box_class incr_box(int* x) {
  invariant integer(x, ?value);
  
  action increase(int amount);
    requires 0 <= amount;
    ensures value == old_value + amount;
    
  handle_predicate observed(int myvalue) {
    invariant myvalue <= value;
    
    preserved_by increase(amount) { }
  }
}
@*/

//@ predicate_family_instance thread_run_data(inc)(int* x) = [1/2]incr_box(?id, x);

void inc(int* x) //@ : thread_run
  //@ requires thread_run_data(inc)(x);
  //@ ensures true;
{
  //@ open thread_run_data(inc)(x);
  //@ assert [?f]incr_box(?id, x);
  //@ handle ha = create_handle incr_box_handle(id);
  while(true)
    //@ invariant [f]incr_box(id, x) &*& incr_box_handle(ha, id);
  {;
    /*@
    consuming_box_predicate incr_box(id, x)
    consuming_handle_predicate incr_box_handle(ha)
    perform_action increase(1) atomic
    {
      @*/ atomic_increment(x); /*@
    }
    producing_handle_predicate incr_box_handle();
    @*/
  }
}

void reader(int* x)
  //@ requires [1/2]incr_box(?id, x);
  //@ ensures false;
{;
  //@ handle ha = create_handle incr_box_handle(id);
  /*@
  consuming_box_predicate incr_box(id, x)
  consuming_handle_predicate incr_box_handle(ha)
  perform_action increase(0) atomic
  {
    @*/ int value = atomic_load_int(x); /*@
  }
  producing_handle_predicate observed(value);
  @*/
  while(true)
    //@ invariant [1/2]incr_box(id, x) &*& observed(ha, id, value);
  {;
    /*@
    consuming_box_predicate incr_box(id, x)
    consuming_handle_predicate observed(ha, value)
    perform_action increase(0) atomic
    {
      @*/ int tmp = atomic_load_int(x); /*@
    }
    producing_handle_predicate observed(tmp);
    @*/
    assert value <= tmp;
    value = tmp;
  }
}

int main()
  //@ requires true;
  //@ ensures true;
{
  int x;
  //@ create_box id = incr_box(&x);
  //@ close thread_run_data(inc)(&x);
  thread_start(inc, &x);
  reader(&x);
  return 0;
}