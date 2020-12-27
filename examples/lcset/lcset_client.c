// Client program that exercises the LCSet module.
// One thread adds all integers starting from a user-provided integer, in order.
// The other thread repeatedly asks the user for a value, then tries to remove it until it succeeds, then tries to remove it again.
// Asserts that the last remove attempt fails.

#include "stdlib.h"
#include "lcset.h"
#include "threading.h"
#include "assert.h"
//@ #include "ghost_cells.gh"

int readNumber() // Asks the user to enter a number.
    //@ requires true;
    //@ ensures INT_MIN < result &*& result < INT_MAX;
{
    abort(); // TODO: Implement this function.
}

/*@

lemma void mem_sorted_add_sorted(list<int> xs, int x1, int x2)
    requires true;
    ensures mem_sorted(x1, add_sorted(x2, xs)) == (x1 == x2 || mem_sorted(x1, xs));
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (h < x2) {
                if (h == x1) {
                } else {
                    mem_sorted_add_sorted(t, x1, x2);
                }
            } else if (h == x2) {
            } else {
            }
    }
}

lemma void not_mem_sorted_remove_sorted(list<int> xs, int x)
    requires !mem_sorted(x, xs) == true;
    ensures remove_sorted(x, xs) == xs;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (h < x) {
                not_mem_sorted_remove_sorted(t, x);
            } else if (h == x) {
            } else {
            }
    }
}

fixpoint bool is_sorted_above(list<int> xs, int x0) {
    switch (xs) {
        case nil: return true;
        case cons(h, t): return x0 < h && is_sorted_above(t, h);
    }
}

lemma void is_sorted_above_above(list<int> xs, int x0, int x1)
    requires is_sorted_above(xs, x0) == true &*& x1 <= x0;
    ensures is_sorted_above(xs, x1) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
    }
}

lemma void is_sorted_add_sorted(list<int> xs, int x0, int x1)
    requires is_sorted_above(xs, x0) == true &*& x0 < x1;
    ensures is_sorted_above(add_sorted(x1, xs), x0) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (x1 < h) {
            } else if (x1 == h) {
            } else {
                is_sorted_add_sorted(t, h, x1);
            }
    }
}

lemma void is_sorted_remove_sorted(list<int> xs, int x0, int x1)
    requires is_sorted_above(xs, x0) == true;
    ensures is_sorted_above(remove_sorted(x1, xs), x0) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (x1 < h) {
            } else if (x1 == h) {
                is_sorted_above_above(t, h, x0);
            } else {
                is_sorted_remove_sorted(t, h, x1);
            }
    }
}

lemma void mem_sorted_remove_sorted(int x00, int x0, int x1, list<int> xs)
    requires is_sorted_above(xs, x00) == true;
    ensures mem_sorted(x0, remove_sorted(x1, xs)) == (mem_sorted(x0, xs) && x1 != x0);
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (x1 < h) {
            } else if (x1 == h) {
                if (x0 < h) {
                    switch (t) { case nil: case cons(th, tt): }
                } else if (x0 == h) {
                    switch (t) { case nil: case cons(th, tt): }
                } else {
                }
            } else {
                if (x0 < h) {
                } else if (x0 == h) {
                } else {
                    mem_sorted_remove_sorted(h, x0, x1, t);
                }
            }
    }
}

lemma void forall_ge_add_sorted(list<int> xs, int u1, int u2)
    requires forall(xs, (ge)(unit, u1)) == true &*& u1 <= u2;
    ensures forall(add_sorted(u2, xs), (ge)(unit, u2)) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (h < u2) {
                forall_ge_add_sorted(t, u1, u2);
            }
    }
}

lemma void forall_remove_sorted(list<int> xs, int x, fixpoint(int, bool) p)
    requires forall(xs, p) == true;
    ensures forall(remove_sorted(x, xs), p) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (h < x) {
                forall_remove_sorted(t, x, p);
            } else if (h == x) {
            } else {
            }
    }
}

lemma void forall_mem_sorted(list<int> xs, int x, fixpoint(int, bool) p)
    requires forall(xs, p) == true &*& mem_sorted(x, xs) == true;
    ensures p(x) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (h < x) {
                forall_mem_sorted(t, x, p);
            } else if (h == x) {
            } else {
            }
    }
}

fixpoint bool ge(unit u, int x, int y) {
    switch (u) {
        case unit: return x >= y;
    }
}

predicate_ctor space_inv(struct set *set, int adderCell, int removerPhaseCell, int removerCell)() =
    set_atomic(set, ?values) &*& is_sorted_above(values, INT_MIN) == true &*&
    [1/2]ghost_cell<int>(adderCell, ?adderValue) &*& forall(values, (ge)(unit, adderValue)) == true &*&
    [1/2]ghost_cell<bool>(removerPhaseCell, ?success) &*&
    [1/2]ghost_cell<int>(removerCell, ?removerValue) &*&
    success ? removerValue <= adderValue &*& !mem_sorted(removerValue, values) : true;

inductive space_info = space_info(struct set *set, int adderCell, int removerPhaseCell, int removerCell);

predicate_family_instance set_sep(space_sep)(space_info info, struct set *set, predicate() inv, set_unsep *unsep) =
    switch (info) {
        case space_info(set_, adderCell, removerPhaseCell, removerCell): return
            set == set_ &*& inv == space_inv(set, adderCell, removerPhaseCell, removerCell) &*& unsep == space_unsep;
    };

predicate_family_instance set_unsep(space_unsep)(space_info info, struct set *set, predicate() inv, set_sep *sep, list<int> values) =
    switch (info) {
        case space_info(set_, adderCell, removerPhaseCell, removerCell): return
            set == set_ &*&
            inv == space_inv(set, adderCell, removerPhaseCell, removerCell) &*& sep == space_sep &*&
            is_sorted_above(values, INT_MIN) == true &*&
            [1/2]ghost_cell<int>(adderCell, ?adderValue) &*& forall(values, (ge)(unit, adderValue)) == true &*&
            [1/2]ghost_cell<bool>(removerPhaseCell, ?success) &*&
            [1/2]ghost_cell<int>(removerCell, ?removerValue) &*&
            success ? removerValue <= adderValue &*& !mem_sorted(removerValue, values) : true;
    };

lemma void space_sep() : set_sep
    requires set_sep(space_sep)(?info, ?set, ?inv, ?unsep) &*& inv();
    ensures set_unsep(unsep)(info, set, inv, space_sep, ?values) &*& set_atomic(set, values);
{
    open set_sep(space_sep)(?info_, set, inv, unsep);
    switch (info_) {
        case space_info(set_, adderCell, removerPhaseCell, removerCell):
            open space_inv(set, adderCell, removerPhaseCell, removerCell)();
            assert set_atomic(set, ?values);
            close set_unsep(space_unsep)(info_, set, inv, space_sep, values);
    }
}

lemma void space_unsep() : set_unsep
    requires set_unsep(space_unsep)(?info, ?set, ?inv, ?sep, ?values) &*& set_atomic(set, values);
    ensures set_sep(sep)(info, set, inv, space_unsep) &*& inv();
{
    open set_unsep(space_unsep)(?info_, set, inv, sep, values);
    switch (info_) {
        case space_info(set_, adderCell, removerPhaseCell, removerCell):
            close space_inv(set, adderCell, removerPhaseCell, removerCell)();
            close set_sep(space_sep)(info_, set, inv, space_unsep);
    }
}

predicate cells(int adderCell, int removerPhaseCell, int removerCell) = true;

predicate_family_instance thread_run_data(adder_thread)(struct set *set) =
    cells(?adderCell, ?removerPhaseCell, ?removerCell) &*&
    [1/2]atomic_space(space_inv(set, adderCell, removerPhaseCell, removerCell)) &*&
    [1/2]ghost_cell<int>(adderCell, INT_MIN) &*&
    [_]set(set);

@*/

void adder_thread(struct set *set) //@ : thread_run
    //@ requires thread_run_data(adder_thread)(set);
    //@ ensures true;
{
    //@ open thread_run_data(adder_thread)(set);
    //@ open cells(?adderCell, ?removerPhaseCell, ?removerCell);
    int x = readNumber();
    for (;;)
        //@ invariant [_]set(set) &*& [1/2]atomic_space(space_inv(set, adderCell, removerPhaseCell, removerCell)) &*& [1/2]ghost_cell<int>(adderCell, ?adderValue) &*& adderValue < x &*& INT_MIN <= adderValue;
    {
        if (INT_MAX <= x) abort();
        {
            /*@
            predicate_family_instance set_add_pre(add_op)(set_unsep *unsep, space_info info, int e) =
                unsep == space_unsep &*& info == space_info(set, adderCell, removerPhaseCell, removerCell) &*& e == x &*&
                [1/2]ghost_cell<int>(adderCell, adderValue);
            predicate_family_instance set_add_post(add_op)(bool result) =
                [1/2]ghost_cell<int>(adderCell, x);
            lemma void add_op() : set_add
                requires set_add_pre(add_op)(?unsep, ?info, ?e) &*& set_unsep(unsep)(info, ?set_, ?inv, ?sep, ?values);
                ensures set_add_post(add_op)(!mem_sorted(e, values)) &*& set_unsep(unsep)(info, set_, inv, sep, add_sorted(e, values));
            {
                open set_add_pre(add_op)(_, _, _);
                open set_unsep(space_unsep)(?info_, _, _, _, _);
                ghost_cell_mutate<int>(adderCell, x);
                close set_add_post(add_op)(!mem_sorted(e, values));
                forall_ge_add_sorted(values, adderValue, x);
                assert [1/2]ghost_cell<int>(removerCell, ?removerValue);
                mem_sorted_add_sorted(values, removerValue, x);
                is_sorted_add_sorted(values, INT_MIN, e);
                close set_unsep(space_unsep)(info_, set, inv, sep, add_sorted(e, values));
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(space_sep);
            //@ produce_lemma_function_pointer_chunk(space_unsep);
            //@ close set_sep(space_sep)(space_info(set, adderCell, removerPhaseCell, removerCell), set, space_inv(set, adderCell, removerPhaseCell, removerCell), space_unsep);
            //@ produce_lemma_function_pointer_chunk(add_op);
            //@ close set_add_pre(add_op)(space_unsep, space_info(set, adderCell, removerPhaseCell, removerCell), x);
            add(set, x);
            //@ open set_add_post(add_op)(_);
            //@ open set_sep(space_sep)(_, _, _, _);
            //@ leak is_set_sep(space_sep);
            //@ leak is_set_unsep(space_unsep);
            //@ leak is_set_add(add_op);
        }
        x++;
    }
}

/*@

lemma void kill_is_set_remove()
    requires is_set_remove(_);
    ensures true;
{
    leak is_set_remove(_);
}

@*/

void remover_thread(struct set *set)
    /*@
    requires
        [_]set(set) &*& cells(?adderCell, ?removerPhaseCell, ?removerCell) &*&
        [1/2]atomic_space(space_inv(set, adderCell, removerPhaseCell, removerCell)) &*&
        [1/2]ghost_cell<bool>(removerPhaseCell, false) &*&
        [1/2]ghost_cell<int>(removerCell, _);
    @*/
    //@ ensures false;
{
    //@ open cells(adderCell, removerPhaseCell, removerCell);
    for (;;)
        //@ invariant [_]set(set) &*& [1/2]atomic_space(space_inv(set, adderCell, removerPhaseCell, removerCell)) &*& [1/2]ghost_cell<bool>(removerPhaseCell, false) &*& [1/2]ghost_cell<int>(removerCell, _);
    {
        int x = readNumber();
        for (;;)
            //@ invariant [_]set(set) &*& [1/2]atomic_space(space_inv(set, adderCell, removerPhaseCell, removerCell)) &*& [1/2]ghost_cell<bool>(removerPhaseCell, false) &*& [1/2]ghost_cell<int>(removerCell, _);
        {
            bool success;
            {
                /*@
                predicate_family_instance set_remove_pre(remove_op)(set_unsep *unsep, space_info info_, int e) =
                    unsep == space_unsep &*& info_ == space_info(set, adderCell, removerPhaseCell, removerCell) &*& e == x &*&
                    [1/2]ghost_cell<bool>(removerPhaseCell, false) &*& [1/2]ghost_cell<int>(removerCell, _);
                predicate_family_instance set_remove_post(remove_op)(bool result) =
                    [1/2]ghost_cell<bool>(removerPhaseCell, result) &*&
                    [1/2]ghost_cell<int>(removerCell, x);
                lemma void remove_op() : set_remove
                    requires set_remove_pre(remove_op)(?unsep, ?info_, ?e) &*& set_unsep(unsep)(info_, ?set_, ?inv, ?sep, ?values);
                    ensures set_remove_post(remove_op)(mem_sorted(e, values)) &*& set_unsep(unsep)(info_, set_, inv, sep, remove_sorted(e, values));
                {
                    open set_remove_pre(remove_op)(_, _, _);
                    open set_unsep(space_unsep)(?info__, _, _, _, _);
                    ghost_cell_mutate(removerCell, x);
                    assert [1/2]ghost_cell(adderCell, ?adderValue);
                    if (mem_sorted(x, values)) {
                        ghost_cell_mutate(removerPhaseCell, true);
                        mem_sorted_remove_sorted(INT_MIN, x, x, values);
                        forall_mem_sorted(values, x, (ge)(unit, adderValue));
                    }
                    forall_remove_sorted(values, x, (ge)(unit, adderValue));
                    close set_remove_post(remove_op)(mem_sorted(e, values));
                    is_sorted_remove_sorted(values, INT_MIN, e);
                    close set_unsep(space_unsep)(info__, set, inv, sep, remove_sorted(e, values));
                }
                @*/
                //@ produce_lemma_function_pointer_chunk(space_sep);
                //@ produce_lemma_function_pointer_chunk(space_unsep);
                //@ close set_sep(space_sep)(space_info(set, adderCell, removerPhaseCell, removerCell), set, space_inv(set, adderCell, removerPhaseCell, removerCell), space_unsep);
                //@ produce_lemma_function_pointer_chunk(remove_op);
                //@ close set_remove_pre(remove_op)(space_unsep, space_info(set, adderCell, removerPhaseCell, removerCell), x);
                success = remove(set, x);
                //@ open set_remove_post(remove_op)(_);
                //@ open set_sep(space_sep)(_, _, _, _);
                //@ kill_is_set_remove();
            }
            if (success) {
                bool success2;
                {
                    /*@
                    predicate_family_instance set_contains_pre(contains_op)(set_unsep *unsep, space_info info_, int e) =
                        unsep == space_unsep &*& info_ == space_info(set, adderCell, removerPhaseCell, removerCell) &*& e == x &*&
                        [1/2]ghost_cell<bool>(removerPhaseCell, true) &*& [1/2]ghost_cell<int>(removerCell, x);
                    predicate_family_instance set_contains_post(contains_op)(bool result) =
                        [1/2]ghost_cell<bool>(removerPhaseCell, false) &*&
                        [1/2]ghost_cell<int>(removerCell, x) &*& !result;
                    lemma void contains_op() : set_contains
                        requires set_contains_pre(contains_op)(?unsep, ?info_, ?e) &*& set_unsep(unsep)(info_, ?set_, ?inv, ?sep, ?values);
                        ensures set_contains_post(contains_op)(mem_sorted(e, values)) &*& set_unsep(unsep)(info_, set_, inv, sep, values);
                    {
                        open set_contains_pre(contains_op)(_, _, _);
                        open set_unsep(space_unsep)(?info__, _, _, _, _);
                        ghost_cell_mutate(removerPhaseCell, false);
                        assert [1/2]ghost_cell<int>(adderCell, ?adderValue);
                        close set_contains_post(contains_op)(mem_sorted(e, values));
                        close set_unsep(space_unsep)(info__, set, inv, sep, values);
                    }
                    @*/
                    //@ close set_sep(space_sep)(space_info(set, adderCell, removerPhaseCell, removerCell), set, space_inv(set, adderCell, removerPhaseCell, removerCell), space_unsep);
                    //@ produce_lemma_function_pointer_chunk(contains_op);
                    //@ close set_contains_pre(contains_op)(space_unsep, space_info(set, adderCell, removerPhaseCell, removerCell), x);
                    success2 = contains(set, x);
                    //@ open set_contains_post(contains_op)(_);
                    //@ open set_sep(space_sep)(_, _, _, _);
                    //@ leak is_set_contains(contains_op);
                }
                assert(!success2);
            }
            //@ leak is_set_sep(space_sep);
            //@ leak is_set_unsep(space_unsep);
        }
    }
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct set *set = create_set();
    //@ int adderCell = create_ghost_cell<int>(INT_MIN);
    //@ int removerPhaseCell = create_ghost_cell<bool>(false);
    //@ int removerCell = create_ghost_cell<int>(0);
    //@ close space_inv(set, adderCell, removerPhaseCell, removerCell)();
    //@ create_atomic_space(space_inv(set, adderCell, removerPhaseCell, removerCell));
    //@ close cells(adderCell, removerPhaseCell, removerCell);
    //@ leak set(set);
    //@ close thread_run_data(adder_thread)(set);
    thread_start(adder_thread, set);
    //@ close cells(adderCell, removerPhaseCell, removerCell);
    remover_thread(set);
}
