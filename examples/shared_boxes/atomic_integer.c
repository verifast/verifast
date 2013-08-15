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

predicate atomic_integer(int* i, real level, predicate(int) I) =
  atomic_integer_box(?id, i, I) &*& box_level(id) == level;
  
lemma void create_atomic_integer(int* i, real upper_bound, predicate(int) I)
  requires integer(i, ?value) &*& I(value);
  ensures atomic_integer(i, ?new_level, I) &*& new_level < upper_bound;
{
  create_box id = atomic_integer_box(i, I) below upper_bound;
  close atomic_integer(i, box_level(id), I);
}
@*/

void atomic_integer_set(int* i, int v)
  //@ requires [?f]atomic_integer(i, ?level, ?I) &*& is_atomic_integer_set_lemma(?lem, v, I, level)  &*& atomic_integer_set_pre(lem)(v);
  //@ ensures [f]atomic_integer(i, level, I) &*& atomic_integer_set_post(lem)(_, v);
{
  ;
  //@ open [f]atomic_integer(i, level, I);
  //@ assert [f]atomic_integer_box(?id, i, I);
  //@ handle ha = create_handle atomic_integer_box_handle(id);
  /*@ consuming_box_predicate atomic_integer_box(id, i, I)
  consuming_handle_predicate atomic_integer_box_handle(ha)
  perform_action set(v)
  {
    @*/ atomic_set_int(i, v); /*@
    lem();
  };
  @*/
  //@ close [f]atomic_integer(i, level, I);
  //@ leak is_atomic_integer_set_lemma(lem, v, I, level);
}

int atomic_integer_get(int* i)
  //@ requires [?f]atomic_integer(i, ?level, ?I) &*& is_atomic_integer_get_lemma(?lem, I, level)  &*& atomic_integer_get_pre(lem)();
  //@ ensures [f]atomic_integer(i, level, I) &*& atomic_integer_get_post(lem)(result);
{
  ;
  //@ open [f]atomic_integer(i, level, I);
  //@ assert [f]atomic_integer_box(?id, i, I);
  /*@ consuming_box_predicate atomic_integer_box(id, i, I)
  perform_action get()
  {
    @*/ int res = atomic_load_int(i); /*@
    lem();
  };
  @*/
  //@ close [f]atomic_integer(i, level, I);
  //@ leak is_atomic_integer_get_lemma(lem, I, level);
  return res;
}

bool atomic_integer_cas(int* i, int old, int new)
  //@ requires [?f]atomic_integer(i, ?level, ?I) &*& is_atomic_integer_cas_lemma(?lem, I, old, new, level)  &*& atomic_integer_cas_pre(lem)(old, new);
  //@ ensures [f]atomic_integer(i, level, I) &*& atomic_integer_cas_post(lem)(result, old, new);
{
  ;
  //@ open [f]atomic_integer(i, level, I);
  //@ assert [f]atomic_integer_box(?id, i, I);
  /*@ consuming_box_predicate atomic_integer_box(id, i, I)
  perform_action cas(old, new)
  {
    @*/ int res = atomic_compare_and_set_int(i, old, new); /*@
    lem();
  };
  @*/
  //@ close [f]atomic_integer(i, level, I);
  //@ leak is_atomic_integer_cas_lemma(lem, I, old, new, level);
  return res == old;
}

/*@
lemma void atomic_integer_dispose(int* i)
  requires atomic_integer(i, ?level, ?I);
  ensures integer(i, ?value) &*& I(value);
{
  open atomic_integer(i, level, I);
  assert atomic_integer_box(?id, i, I);
  dispose_box atomic_integer_box(id, i, I);
}
@*/

