#include "atomics.h"
#include "atomic_integer.h"

/*@
box_class atomic_integer_box(int* i, predicate(int) I) {
  invariant integer(i, ?value) &*& I(value);
  
  action set(int new_value);
    requires true;
    ensures value == new_value;
  
  action get();
    requires true;
    ensures value == old_value;
  
  action cas(int old, int new);
    requires true;
    ensures old_value == old ? value == new : value == old_value;
     
}

predicate atomic_integer(int* i, predicate(int) I) =
  atomic_integer_box(?id, i, I);
  
lemma void create_atomic_integer(int* i, predicate(int) I)
  requires integer(i, ?value) &*& I(value);
  ensures atomic_integer(i, I);
{
  create_box id = atomic_integer_box(i, I);
  close atomic_integer(i, I);
}
@*/

void atomic_integer_set(int* i, int v)
  //@ requires [?f]atomic_integer(i, ?I) &*& is_atomic_integer_set_lemma(?lem, v, I)  &*& atomic_integer_set_pre(lem)(v);
  //@ ensures [f]atomic_integer(i, I) &*& atomic_integer_set_post(lem)(_, v);
{
  ;
  //@ open [f]atomic_integer(i, I);
  //@ assert [f]atomic_integer_box(?id, i, I);
  //@ handle ha = create_handle atomic_integer_box_handle(id);
  /*@ consuming_box_predicate atomic_integer_box(id, i, I)
  consuming_handle_predicate atomic_integer_box_handle(ha)
  perform_action set(v) atomic
  {
    @*/ atomic_set_int(i, v); /*@
    lem();
  }
  producing_handle_predicate atomic_integer_box_handle();
  @*/
  //@ close [f]atomic_integer(i, I);
  //@ leak atomic_integer_box_handle(ha, id);
  //@ leak is_atomic_integer_set_lemma(lem, v, I);
}

int atomic_integer_get(int* i)
  //@ requires [?f]atomic_integer(i, ?I) &*& is_atomic_integer_get_lemma(?lem, I)  &*& atomic_integer_get_pre(lem)();
  //@ ensures [f]atomic_integer(i, I) &*& atomic_integer_get_post(lem)(result);
{
  ;
  //@ open [f]atomic_integer(i, I);
  //@ assert [f]atomic_integer_box(?id, i, I);
  //@ handle ha = create_handle atomic_integer_box_handle(id);
  /*@ consuming_box_predicate atomic_integer_box(id, i, I)
  consuming_handle_predicate atomic_integer_box_handle(ha)
  perform_action get() atomic
  {
    @*/ int res = atomic_load_int(i); /*@
    lem();
  }
  producing_handle_predicate atomic_integer_box_handle();
  @*/
  //@ close [f]atomic_integer(i, I);
  //@ leak atomic_integer_box_handle(ha, id);
  //@ leak is_atomic_integer_get_lemma(lem, I);
  return res;
}

