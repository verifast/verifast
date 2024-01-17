#ifndef PRELUDE_RUST_H
#define PRELUDE_RUST_H

#include "rust/rust_belt/general.h"
//@ #include "prelude_rust_core.gh"
//@ #include "rust/rust_belt/lifetime_logic.gh"

union std_empty_ {};
struct std_tuple_0_ {};

typedef int main(int argc, char **argv);
    //@ requires 0 <= argc &*& [_]argv(argv, argc, ?arguments);
    //@ ensures junk();

/* TODO @Nima: In Rust main function's return type should implement std::process::Termination.
() type implements it for example. Until we support traits we will just support main functions with
unit as their return type.
*/

typedef struct std_tuple_0_ main_full/*@(int mainModule)@*/(int argc, char **argv);
    //@ requires thread_token(?_t) &*& module(mainModule, true) &*& 0 <= argc &*& [_]argv(argv, argc, ?arguments);
    //@ ensures thread_token(_t) &*& junk();

// Specify custom_main_spec on your main function to override the main_full default
typedef int custom_main_spec(int argc, char **argv);
    //@ requires false;
    //@ ensures true;

// action permissions

/*@
fixpoint bool is_action_permission0(predicate(box;) p);

lemma void action_permission0_unique(predicate(box;) p, box id);
  requires [?f]p(id) &*& is_action_permission0(p) == true;
  ensures [f]p(id) &*& f <= 1;
  
fixpoint bool is_action_permission1_dispenser<t>(predicate(box, list<t>) p);
fixpoint predicate(box, t) get_action_permission1_for_dispenser<t>(predicate(box, list<t>) p);

lemma void action_permission1_split<t>(predicate(box, list<t>) dispenser, predicate(box, t) p, box id, t x);
  requires is_action_permission1_dispenser(dispenser) == true &*& dispenser(id, ?used) &*& ! mem(x, used) &*& get_action_permission1_for_dispenser(dispenser) == p;
  ensures dispenser(id, cons(x, used)) &*& p(id, x);

lemma void action_permission1_split2<t>(predicate(box, list<t>) dispenser, predicate(box, t) p, box id, t x);
  requires is_action_permission1_dispenser(dispenser) == true &*& dispenser(id, ?used) &*& ! mem(x, used) &*& get_action_permission1_for_dispenser(dispenser) == p;
  ensures dispenser(id, append(used, cons(x, nil))) &*& p(id, x);

lemma void action_permission1_merge<t>(predicate(box, list<t>) dispenser, predicate(box, t) p, box id, t x);
  requires is_action_permission1_dispenser(dispenser) == true &*& dispenser(id, ?used) &*& get_action_permission1_for_dispenser(dispenser) == p &*& p(id, x);
  ensures dispenser(id, remove(x, used));
  
fixpoint bool is_action_permission1<t>(predicate(box, t;) p);

lemma void action_permission1_unique<t>(predicate(box, t;) p, box id, t x);
  requires [?f]p(id, x) &*& is_action_permission1<t>(p) == true;
  ensures [f]p(id, x) &*& f <= 1;
  
predicate is_handle(handle ha);

lemma void is_handle_unique(handle ha1, handle ha2);
  requires is_handle(ha1) &*& is_handle(ha2);
  ensures is_handle(ha1) &*& is_handle(ha2) &*& ha1 != ha2;

lemma void box_level_unique(box id1, box id2);
  requires id1 != id2;
  ensures box_level(id1) != box_level(id2);

fixpoint real box_level(box id);

predicate current_box_level(real level);
@*/

/*@

// Fixpoint operator, for defining functions by well-founded recursion over the nonnegative integers

fixpoint b fix<a, b>(fixpoint(fixpoint(a, b), a, b) def, fixpoint(a, int) measure, a x);

// A proof of this lemma is in examples/wf_func_proof.c

lemma void fix_unfold<a, b>(fixpoint(fixpoint(a, b), a, b) def, fixpoint(a, int) measure, a x0);
    requires 0 <= measure(x0) && fix(def, measure, x0) != def((fix)(def, measure), x0);
    ensures
        exists<pair<pair<fixpoint(a, b), fixpoint(a, b)>, a> >(pair(pair(?f1, ?f2), ?a)) &*&
        forall_(a x; measure(x) < 0 || measure(a) <= measure(x) || f1(x) == f2(x)) &*&
        0 <= measure(a) &*&
        def(f1, a) != def(f2, a);

@*/

#endif
