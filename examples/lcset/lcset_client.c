#include "lcset.h"

/*@

predicate_family thread_run_pre(void *run)(void *data);
predicate_family thread_run_post(void *run)(void *data);

predicate thread(struct thread *thread, thread_run *run, void *data);

@*/

typedef void thread_run(void *data);
    //@ requires thread_run_pre(this)(data);
    //@ ensures thread_run_post(this)(data);

struct thread;

struct thread *thread_start(thread_run *run, void *data);
    //@ requires is_thread_run(run) == true &*& thread_run_pre(run)(data);
    //@ ensures thread(result, run, data);

void thread_join(struct thread *thread);
    //@ requires thread(thread, ?run, ?data);
    //@ ensures thread_run_post(run)(data);

int readNumber();
    //@ requires true;
    //@ ensures INT_MIN < result &*& result < INT_MAX;

/*@
inductive set_info = set_info(struct set *);

predicate_ctor set_ctor(struct set *set)() = set_atomic(set, _);

predicate_family_instance thread_run_pre(session)(struct set *set) =
    [1/2]set(set) &*& [1/2]atomic_space(set_ctor(set));
predicate_family_instance thread_run_post(session)(struct set *set) =
    [1/2]set(set) &*& [1/2]atomic_space(set_ctor(set));
@*/

void session(struct set *set) //@ : thread_run
    //@ requires thread_run_pre(session)(set);
    //@ ensures thread_run_post(session)(set);
{
    //@ open thread_run_pre(session)(set);
    
    // Read a number from the user.
    int x = readNumber();
    
    {
        /*@
        predicate_family_instance set_sep(sep)(set_info info, struct set *set_, predicate() inv, set_unsep *unsep_) =
            info == set_info(set) &*& inv == set_ctor(set) &*& set_ == set &*& unsep_ == unsep;
        predicate_family_instance set_unsep(unsep)(set_info info, struct set *set_, predicate() inv, set_sep *sep_, list<int> xs) =
            info == set_info(set) &*& inv == set_ctor(set) &*& set_ == set &*& sep_ == sep;
        lemma void sep() : set_sep
            requires set_sep(sep)(?info, ?set_, ?inv, ?unsep_) &*& inv();
            ensures set_unsep(unsep_)(info, set_, inv, sep, ?values) &*& set_atomic(set_, values);
        {
            open set_sep(sep)(_, _, _, _);
            open set_ctor(set)();
            assert set_atomic(set, ?values);
            close set_unsep(unsep)(set_info(set), set, set_ctor(set), sep, values);
        }
        lemma void unsep() : set_unsep
            requires set_unsep(unsep)(?info, ?set_, ?inv, ?sep_, ?values) &*& set_atomic(set_, values);
            ensures set_sep(sep_)(info, set_, inv, unsep) &*& inv();
        {
            open set_unsep(unsep)(_, _, _, _, _);
            close set_ctor(set)();
            close set_sep(sep)(set_info(set), set, set_ctor(set), unsep);
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(sep);
        //@ produce_lemma_function_pointer_chunk(unsep);
        // Try to acquire the number.
    loop:
        /*@
        invariant
            is_set_sep(sep) &*& is_set_unsep(unsep) &*& [1/2]set(set) &*& [1/2]atomic_space(set_ctor(set));
        @*/
        {
            /*@
            predicate_family_instance set_add_pre(addOp)(set_unsep *unsep_, set_info info, int e) =
                unsep_ == unsep &*& info == set_info(set) &*& e == x;
            predicate_family_instance set_add_post(addOp)(bool success) = true;
            lemma void addOp() : set_add
                requires set_add_pre(addOp)(?unsep_, ?info, ?e) &*& set_unsep(unsep_)(info, ?set_, ?inv, ?sep_, ?values);
                ensures set_add_post(addOp)(!mem_sorted(e, values)) &*& set_unsep(unsep_)(info, set_, inv, sep_, add_sorted(e, values));
            {
                open set_add_pre(addOp)(_, _, _);
                open set_unsep(unsep)(_, _, _, _, _);
                close set_add_post(addOp)(!mem_sorted(e, values));
                close set_unsep(unsep)(set_info(set), set, set_ctor(set), sep, add_sorted(x, values));
            }
            @*/
            //@ close set_sep(sep)(set_info(set), set, set_ctor(set), unsep);
            //@ close set_add_pre(addOp)(unsep, set_info(set), x);
            //@ produce_lemma_function_pointer_chunk(addOp);
            bool result = add(set, x);
            //@ leak is_set_add(addOp);
            //@ open set_sep(sep)(_, _, _, _);
            //@ open set_add_post(addOp)(_);
            if (!result) goto loop;
        }
        
        // We have the number.
        
        // Release the number.
        {
            /*@
            predicate_family_instance set_remove_pre(removeOp)(set_unsep *unsep_, set_info info, int e) =
                unsep_ == unsep &*& info == set_info(set) &*& e == x;
            predicate_family_instance set_remove_post(removeOp)(bool success) = true;
            lemma void removeOp() : set_remove
                requires set_remove_pre(removeOp)(?unsep_, ?info, ?e) &*& set_unsep(unsep_)(info, ?set_, ?inv, ?sep_, ?values);
                ensures set_remove_post(removeOp)(mem_sorted(e, values)) &*& set_unsep(unsep_)(info, set_, inv, sep_, remove_sorted(e, values));
            {
                open set_remove_pre(removeOp)(_, _, _);
                open set_unsep(unsep)(_, _, _, _, _);
                close set_unsep(unsep)(set_info(set), set, set_ctor(set), sep, remove_sorted(e, values));
                close set_remove_post(removeOp)(mem_sorted(e, values));
            }
            @*/
            //@ close set_sep(sep)(set_info(set), set, set_ctor(set), unsep);
            //@ close set_remove_pre(removeOp)(unsep, set_info(set), x);
            //@ produce_lemma_function_pointer_chunk(removeOp);
            remove(set, x);
            //@ leak is_set_remove(removeOp);
            //@ open set_sep(sep)(_, _, _, _);
            //@ open set_remove_post(removeOp)(_);
        }
        //@ leak is_set_sep(sep);
        //@ leak is_set_unsep(unsep);
    }
    //@ close thread_run_post(session)(set);
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct set *set = create_set();
    //@ close set_ctor(set)();
    //@ create_atomic_space(set_ctor(set));
    //@ split_fraction set(set);
    //@ split_fraction atomic_space(set_ctor(set));
    //@ close thread_run_pre(session)(set);
    struct thread *thread1 = thread_start(session, set);
    //@ close thread_run_pre(session)(set);
    struct thread *thread2 = thread_start(session, set);
    thread_join(thread1);
    //@ open thread_run_post(session)(set);
    thread_join(thread2);
    //@ open thread_run_post(session)(set);
    //@ dispose_atomic_space(set_ctor(set));
    //@ open set_ctor(set)();
    dispose_set(set);
    return 0;
}