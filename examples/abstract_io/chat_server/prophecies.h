#ifndef PROPHECIES_H
#define PROPHECIES_H

//@ #include "sequences.gh"

typedef long long int prophecy_var_t;

//@ predicate prophecy_var<t>(prophecy_var_t id; fixpoint(fixpoint(nat, t), bool) p, predicate(void *; t) pred, fixpoint(nat, t) seq);

//@ predicate create_prophecy_var_ghost_args<t>(fixpoint(fixpoint(nat, t), bool) p, fixpoint(nat, t) witness, predicate(void *; t) pred) = true;

prophecy_var_t create_prophecy_var/*@ <t> @*/();
    //@ requires create_prophecy_var_ghost_args<t>(?p, ?witness, ?pred) &*& p(witness) == true; // UNCHECKED REQUIREMENT: 'pred' must not depend on mutable ghost state.
    //@ ensures prophecy_var<t>(result, p, pred, ?seq) &*& p(seq) == true;

//@ predicate prophecy_var_assign_ghost_args<t>(fixpoint(nat, t) witness) = true;

void prophecy_var_assign/*@ <t> @*/(prophecy_var_t prophecyVar, void *value);
    //@ requires prophecy_var<t>(prophecyVar, ?p, ?pred, ?seq) &*& pred(value, ?v) &*& prophecy_var_assign_ghost_args<t>(?witness) &*& p((cons_)(v, witness)) == true;
    //@ ensures prophecy_var<t>(prophecyVar, (contains_cons_)(p, v), pred, (tail_)(seq)) &*& pred(value, v) &*& v == seq(zero);

#endif
