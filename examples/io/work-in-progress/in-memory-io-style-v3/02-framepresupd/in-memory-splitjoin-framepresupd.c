/**
 * In-memory verification approach supporting split-join,
 * based on the frame preserving update idea.
 * Supports:
 * - call i/o-style function from non-io function (close its precondition)
 * - out of postcondition of i/o-style function, the memory is constrained (if all joins have hapened)
 * - suppor split-join
 * - elegant, understandable and actually usable
 * - compositional
 * - modular
 * - nondeterminism is supported
 *
 * Not supported:
 * - if not all splits have joined, assertions cannot constrain the memory
 *   contents at that point (but it can after the joins have happened)
 *
 * Not tested:
 * - nontermination
 */

//@ #include "listex.gh"
#include "in-memory-splitjoin-framepresupd-place.h"

/*@
// -- Place

predicate place_inv(list<place> ts, int state) =
  exists<place>(?t)
  &*& true==mem(t, ts)
  
  &*& place_init_t == place_get_type(t) ?
    ts == cons(t, nil)
    &*& state == place_get_init_state(t)
    
  : place_io_t == place_get_type(t) ?
    exists<int>(?state1)
    &*& true == (place_get_op(t))(state1, state)
    &*& place_inv(cons(place_get_prev(t), remove(t, ts)), state1)
    
  : place_join_t == place_get_type(t) ?
    place_inv(cons(place_get_prev(t), cons(place_get_other_prev(t), remove(t, ts))), state)
  
  : place_split_left_t == place_get_type(t) && mem(place_split_right(place_get_prev(t)), ts)
    || place_split_right_t == place_get_type(t) && mem(place_split_left(place_get_prev(t)), ts) ?
      place_inv(cons(place_get_prev(t), remove(place_split_left(place_get_prev(t)), remove(place_split_right(place_get_prev(t)), ts))), state)
  :
    false
;

lemma void get_place_inv(place t1, int state);
  requires token(?py, t1) &*& get_parent(t1) == none;
  ensures token(py, t1) &*& place_inv(cons(t1, nil), state);

// -- Session
lemma void create_session(int state, predicate(int) invar_phys);
  requires invar_phys(state);
  ensures token(invar_phys, place_init(state)) &*& invar_high(invar_phys, state);

// -- Invars
predicate invar_low(predicate(int) invar_fys, int state); // no body.
predicate invar_high(predicate(int) invar_fys, int state) =
  invar_low(invar_fys, state) &*& invar_fys(state); // user can freely open/close this.

// -- Tokens
predicate token(predicate(int) invar_fys, place t); // no body.

predicate split(place t1, place t2; place t3) =
  t2 == place_split_left(t1)
  &*& t3 == place_split_right(t1)
;
fixpoint option<place> get_parent_of_parent(place t){
  return switch(get_parent(t)){
    case none: return none;
    case some(parent): return get_parent(parent);
  };
}
predicate join(place t1, place t2; place t3) =
  t3 == place_join(get_parent_of_parent(t1), t1, t2)
  &*& get_parent(t1) == get_parent(t2) // if you want postcondition-style i/o, you'll need to add this to precondition of join lemma.
;

lemma void split(place t1);
  requires token(?py, t1) &*& split(t1, ?t2, ?t3);
  ensures token(py, t2) &*& token(py, t3);

lemma void join(place t1, place t2);
  requires token(?py, t1) &*& token(py, t2) &*& join(t1, t2, ?t3);
  ensures token(py, t3);


// -- IO operations
predicate io(place t1, fixpoint(int,int,bool) op; place t2) =
  t2 == place_io(t1, op)
;

lemma void do_io(fixpoint(int state1, int state2, bool) op, int state2);
  requires token(?py, ?t1) &*& invar_low(py, ?state) &*& io(t1, op, ?t2) &*& op(state, state2) == true;
  ensures token(py, t2) &*& invar_low(py, state2);
@*/


// --- Usage example --- //
int buffer;

//@ predicate my_invar_phys(int x) = buffer |-> x;

/*@
fixpoint bool add_something_fp(int add_this, int state1, int state2){
  return state2 == state1 + add_this;
}

predicate add_something_io(place t1, int add_this, place t2) =
  io(t1, (add_something_fp)(add_this), t2);
@*/

void add_something(int add_this)
//@ requires invar_high(my_invar_phys, ?state) &*& token(my_invar_phys, ?t1) &*& add_something_io(t1, add_this, ?t2);
//@ ensures invar_high(my_invar_phys, ?state2) &*& token(my_invar_phys, t2);
{
  //@ open invar_high(_, _);
  //@ open my_invar_phys(_);
  buffer = buffer + add_this;
  //@ close my_invar_phys(_);
  //@ open add_something_io(_, _, _);
  //@ do_io((add_something_fp)(add_this), state + add_this);
  //@ close invar_high(_, _);
}


/*@
fixpoint bool make_minimum_fp(int min, int state1, int state2){
  return
    state2 == state1 && state1 >= min
    || state2 == min && state1 < min
  ;
}

predicate make_minimum_io(place t1, int min, place t2) =
  io(t1, (make_minimum_fp)(min), t2);

@*/

void make_minimum(int min)
//@ requires invar_high(my_invar_phys, ?state) &*& token(my_invar_phys, ?t1) &*& make_minimum_io(t1, min, ?t2);
//@ ensures invar_high(my_invar_phys, ?state2) &*& token(my_invar_phys, t2);
{
  //@ open invar_high(_, _);
  //@ open my_invar_phys(_);
  if (buffer < min){
    buffer = min;
  }
  //@ int buffer_contents = buffer;
  //@ close my_invar_phys(_);
  //@ open make_minimum_io(_, _, _);
  //@ do_io((make_minimum_fp)(min), buffer_contents);
  //@ close invar_high(_, _);
}

//@ predicate tokenwrap(predicate(int) py, place t) = token(py, t);

void splitjoin_example(int add_this, int min)
/*@ requires invar_high(my_invar_phys, ?state) &*& token(my_invar_phys, ?t1)
  &*& split(t1, ?t_add_1, ?t_min_1)
    &*& add_something_io(t_add_1, add_this, ?t_add_2)
    &*& make_minimum_io(t_min_1, min, ?t_min_2)
  &*& join(t_add_2, t_min_2, ?t2);
@*/
//@ ensures invar_high(my_invar_phys, ?state2) &*& token(my_invar_phys, t2);
{
  //@ assert token(my_invar_phys, t1);
  //@ split(t1);

  //@ close tokenwrap(my_invar_phys, t_min_1);
  add_something(add_this);
  //@ open tokenwrap(_, t_min_1);
  
  //@ close tokenwrap(my_invar_phys, t_add_2);
  make_minimum(min);
  //@ open tokenwrap(_, t_add_2);
  
  //@ join(t_add_2, t_min_2);
}

// --- Use I/O from non-I/O --- //

void add_something_no_io(int add_this)
//@ requires buffer |-> ?startvalue;
//@ ensures buffer |-> startvalue + add_this;
{
  //@ close my_invar_phys(startvalue);
  //@ create_session(startvalue, my_invar_phys);
  //@ assert token(_, ?t1);
  //@ close add_something_io(t1, add_this, _);
  add_something(add_this);
  //@ assert token(_, ?t2);
  //@ assert invar_high(_, ?state2);
  //@ get_place_inv(t2, state2);
  //@ open place_inv(_, state2);
  //@ open place_inv(_, ?state_prev);
  //@ open invar_high(_, _);
  //@ open my_invar_phys(_);
  //@ leak invar_low(_, _);
  //@ leak token(_, _);
}

void splitjoin_example_no_io()
//@ requires buffer |-> 4;
//@ ensures buffer |-> ?x &*& x == 25 || x == 20;
{
  //@ close my_invar_phys(4);
  //@ create_session(4, my_invar_phys);
  
  //@ assert token(my_invar_phys, ?t1);
  //@ close split(t1, ?t_add_1, ?t_min_1);
  //@ close add_something_io(t_add_1, 5, ?t_add_2);
  //@ close make_minimum_io(t_min_1, 20, ?t_min_2);
  //@ close join(t_add_2, t_min_2, ?t2);
  splitjoin_example(5, 20);
  
  //@ open invar_high(_, _);
  //@ open my_invar_phys(?cur_val);
  
  //@ get_place_inv(t2, cur_val);
  //@ open place_inv(_, _);
  //@ open place_inv(_, _);  
  //@ open place_inv(_, _);
  //@ open place_inv(_, _);
  //@ open place_inv(_, _);
  
  //@ leak invar_low(_, _);
  //@ leak token(_, _);
}
