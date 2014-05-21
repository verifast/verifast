/**
 * !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
 * If you are looking for examples of I/O, you are at the wrong file.
 * !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
 *
 * This file tries to answer the question "Can we use I/O style contracts
 * for specifying the memory behavior of programs instead of the I/O behavior?".
 *
 * So, if you just want to verify I/O this file is irrelevant to you.
 *
 * The main idea is that we try to write a C implementation of
 * a low-level I/O function that uses memory instead of performing
 * I/O. If we have such a function for reading and one for writing,
 * we can write all other functions on top of it. Because all these functions
 * has an I/O style contract, we then know that the I/O style contracts can
 * be used to verify memory state as well.
 * We choose a function that performs a system call. Because we try to
 * verify memory-behaviour, the function just writes the system call
 * to a buffer (if you want to verify I/O, the function will of course
 * do the system call, but that's not what we try to do here).
 *
 * But how do we make an in-memory implementation of a function with an
 * I/O contract, and how do we give a body to predicates like split and join?
 * The basic idea is as follows.
 * An I/O predicate, like some_io(time t1, some_type some_arguments, time t2)
 * "goes from" a time t1 and "goes to" a time t2.
 * A time-chunk, e.g. time(t1), has a time as argument.
 * A time like e.g. t1 consists of an invariant, a guarantee and a rely.
 * The invariant expresses properties of the current time.
 * Example: for the chunk print_char(t1, 'a', t2) the
 * time t2 expresses the invariant that there must be an 'a' on
 * the screen. Here the state is what is on the screen.
 * An invariant is thus a function from state to bool.
 * The guarantee expresses the possible state transitions of
 * the current ghost thread (for every time there is what is called here a
 * ghost thread). In the example print_char(t1, 'a', t2) the
 * possible transitions of the old state to the new state is one where
 * 'a' is in the new state. A guarantee is thus a function from state to state to bool.
 * A rely is the transitions (from states to states) that
 * other ghost threads can do. If another ghost thread can write 'b',
 * then the rely will express that this happens.
 * A rely is thus a function from state to state to bool.
 *
 * Currently, only the function to write is implemented and
 * the buffer is only one item big.
 *
 * Launch with: vfide -I . syscall_memory.c
 */

//@ #include "io/io.gh"
//@ #include "helpers/cooked_ghost_lists.gh"
//@ #include <quantifiers.gh>
//@ #include <listex.gh>
//@ #include <arrays.gh>
//@ #include "io/io_pred_bodies.gh"
#include <stdlib.h> // abort
#include <stddef.h>

/*@
fixpoint list<ioaction> iostate_to_list(iostate iostate){
    switch(iostate){
        case iostate(ioactions): return ioactions;
    }
}

fixpoint bool iostate_add(iostate sigma1, iostate sigma2, ioaction act){
    switch(sigma1){
        case iostate(actions): return sigma2 == iostate(cons(act, actions));
    }
}

fixpoint bool syscall_guarantee(int c, fixpoint(iostate, bool) invar, fixpoint(iostate, iostate, bool) guarantee, pair<iostate, iostate > pair){
    return
        snd(pair) == fst(pair) // we're reflexive.
        // it's allowed to add "c":
        || !invar( fst(pair) )
        || ! iostate_add(fst(pair),snd(pair), ioaction({c}))
        || guarantee(fst(pair), snd(pair))
    ;
}

predicate syscall_io(time t1, int c, time t2) =
    t1 == time(?invar1, ?guarantee, ?rely)
    &*& t2 == time(?invar2, guarantee, rely)
    
    &*& [_]is_forall_t<pair<iostate, iostate > >(?forall_sigmapair)
    
    // guarantee is reflexive.
    // guarantee adds a c.
    &*& true == forall_sigmapair((syscall_guarantee)(c, invar1, guarantee))
    
    // invar2 = R({o^v|o \in invar1})
    &*& true == forall_sigmapair((invar2_includes_guarantee)(invar1,invar2,guarantee))
    &*& true == forall_sigmapair((invar_closed_under_rely)(t2))
;

@*/


int *memory;

/*@
fixpoint iostate buffer_to_iostate(int buffer){
    return buffer == 0 ? iostate({}) : iostate({ioaction({buffer})});
}


predicate iostate(int id, iostate state) =
    syscall_iostate(state)
    &*& iothreads(id, state);

predicate syscall_iostate(iostate state) =
    pointer(&memory, ?memory_)
    &*& integer(memory_, ?b)
    &*& state == buffer_to_iostate(b)
;
@*/



void syscall_output(int c)
/*@ requires
    syscall_io(?t1, c, ?t2)
    &*& time(?ghost_list_id, t1)
    &*& iostate(ghost_list_id, ?state1)
    
    &*& state1 == iostate(?state1_list)
    
    // For now, the buffer is encoded as one int, and 0 denotes
    // empty buffer. Currently we disallow writing '0'.
    &*& c != 0;
@*/
/*@ ensures
    time(ghost_list_id, t2)
    &*& iostate(ghost_list_id, iostate(append(state1_list, {ioaction({c})})));
@*/
{
    // For now, we assume that the buffer is not full yet
    // (currently the buffer is one element big)
    //@ assume(length(state1_list) < 1);
    
    
    //@ assert (t1 == time(?invar1, ?guarantee, ?rely));
    


    //@ open syscall_io(t1, c, t2);
    //@ open time(ghost_list_id, t1);
    //@ open iostate(_, _);
    //@ open iothreads(ghost_list_id, state1);
    //@ open syscall_iostate(state1);
    //@ assert pointer(&memory, ?memory_) &*& integer(memory_, 0);
    //@ assert cooked_ghost_list(ghost_list_id, _, ?k_time_pairs_old);
    //@ assert cooked_ghost_list_member_handle(ghost_list_id, ?k_t1, t1);
    //@ cooked_ghost_list_match(ghost_list_id, k_t1);
    
    *memory = c;
    //@ cooked_ghost_list_remove(ghost_list_id, k_t1);
    //@ cooked_ghost_list_add(ghost_list_id, t2);
    
    // Initialize handy variables:
    //@ assert cooked_ghost_list(ghost_list_id, ?k_t2_plus_1, ?k_time_pairs_new);
    //@ int k_t2 = k_t2_plus_1 - 1;
    //@ assert [_]is_forall_t<pair<iostate, iostate > >(?forall_sigmapair);
    //@ iostate state2 = buffer_to_iostate(c);
    //@ iostate sigma = iostate({});
    //@ assert t2 == time(?invar2, guarantee, rely);
    //@ assert [_]is_forall_t<iostate >(?forall_sigma);
    //@ assert [_]is_forall_t< quadruple< pair<int,time>, pair<int, time>, iostate, iostate > >(?forall_guar_rely);
    //@ get_forall_t< triple< pair<int,time>, iostate, iostate > >();
    //@ assert [_]is_forall_t< triple< pair<int,time>, iostate, iostate > >(?forall_triple);
    //@ assert [_]is_forall_t< pair< pair<int,time>, pair<iostate, iostate > > >(?forall_ktimesigmasigma);
    
    // PROOF: for all threads, invar holds for the new state:
        // PROOF: for the current thread, the new invar holds for the new state:
            // PROOF
                //@ forall_elim(k_time_pairs_old, (invar_applies)(state1), pair(k_t1, t1));
            //@ assert true == invar1(state1); // End proof.
            
            // PROOF
                //@ forall_t_elim(forall_sigmapair, ((syscall_guarantee)(c, invar1, guarantee)), pair(state1, state2));
            //@ assert true == guarantee(state1, state2); // End proof.
            
            // PROOF
                //@ forall_t_elim(forall_sigmapair, (invar2_includes_guarantee)(invar1,invar2,guarantee), pair(state1, state2));
            //@ assert true == invar2(state2); // End proof.

        //@ assert true == invar2(state2); // End PROOF.
        
    
        // PROOF: for other threads, invar holds for the new state:
        
            // For all other threads: (state1,state2) is in guarantee of current thread, thus implies rely of ohter threads.
            // Combine this with: rely of one thread preserves invar of said thread.
            
            
            //@ list<pair<int, time> > k_time_pairs_old_rem = remove( pair(k_t1, t1), k_time_pairs_old);
            
            // PROOF: 
                //@ assert k_time_pairs_new == append(remove( pair(k_t1, t1), k_time_pairs_old ), cons(pair(k_t2, t2), nil));
            
                //@ assert true == forall(k_time_pairs_old, (invar_applies)(state1));
                
                //@ forall_remove(k_time_pairs_old, (invar_applies)(state1), pair(k_t1,t1));
                //@ assert (true == forall(remove( pair(k_t1, t1), k_time_pairs_old), (invar_applies)(state1)));
            
            //@ assert (true == forall(k_time_pairs_old_rem, (invar_applies)(state1)));  // End proof.
            
            
            /*@
            {
            
            lemma void invar_state1_impl_invar_state2(list<pair<int, time> > k_time_pairs, list<pair<int, time> > k_time_pairs_short, pair<int, time> activethread)
                requires true == forall(k_time_pairs_short, (invar_applies)(state1))
                    &*& [_]is_forall_t< quadruple< pair<int,time>, pair<int, time>, iostate, iostate > >(forall_guar_rely)
                    &*& true == forall_guar_rely((guarantee_preserve_rely)(k_time_pairs))
                    &*& mem(activethread, k_time_pairs) == true
                    &*& false == mem(activethread, k_time_pairs_short)
                    &*& true == (guarantee_of_time(snd(activethread)))(state1, state2)
                    &*& true == subset(k_time_pairs_short, k_time_pairs)
            
                    &*& [_]is_forall_t< pair< pair<int,time>, pair<iostate, iostate > > >(forall_ktimesigmasigma)
                    &*& true == forall_ktimesigmasigma((rely_preserve_invar)(k_time_pairs))
                    ;
                
                ensures true == forall(k_time_pairs_short, (invar_applies)(state2));
            {
                switch (k_time_pairs_short){
                    case nil:
                    case cons(h,t):
                        quadruple< pair<int,time>, pair<int, time>, iostate, iostate > quadruple = quadruple(activethread, h, state1, state2);
                        forall_t_elim(forall_guar_rely, (guarantee_preserve_rely)(k_time_pairs), quadruple);
                        assert ! mem(quadruple1(quadruple), k_time_pairs)
                            || ! mem(quadruple2(quadruple), k_time_pairs)
                            || ! (quadruple1(quadruple) != quadruple2(quadruple))
                            || ! (guarantee_of_time(snd(quadruple1(quadruple)))) (quadruple3(quadruple), quadruple4(quadruple))
                            || (rely_of_time(snd(quadruple2(quadruple)))) (quadruple3(quadruple), quadruple4(quadruple));
                        assert (quadruple1(quadruple) != quadruple2(quadruple));
                        assert true == (rely_of_time(snd(quadruple2(quadruple)))) (quadruple3(quadruple), quadruple4(quadruple));
                        assert true == (rely_of_time(snd(h))) (state1, state2);
                        
                        pair< pair<int, time>, pair< iostate, iostate > > pair = pair(h, pair(state1, state2)); //triple< pair<int,time>, iostate, iostate > triple = triple(h, state1, state2);
                        forall_t_elim(forall_ktimesigmasigma, (rely_preserve_invar)(k_time_pairs), pair);
                        assert ! mem(h, k_time_pairs)
                            || ! (invar_of_time(snd(h))) (state1)
                            || ! (rely_of_time(snd(h))) (state1, state2)
                            || (invar_of_time(snd(h))) (state1);
                        assert true == (invar_of_time)(snd(h))(state1);
                        
                        assert true == invar_applies(state2, h);
                        
                        invar_state1_impl_invar_state2(k_time_pairs, t, activethread);
                }
            }
            
            assert true == forall_guar_rely((guarantee_preserve_rely)(k_time_pairs_old));
            
            forall_t_elim(forall_sigmapair, (syscall_guarantee)(c, invar1, guarantee), pair(state1, state2));
            assert true == syscall_guarantee(c, invar1, guarantee, pair(state1, state2)); // result of forall_t_elim.
            assert !invar1(state1) || ! ((state2 == iostate(cons(ioaction({c}), iostate_to_list(state1)))) || state2 == state1 ) || guarantee(state1,state2); // body of previous line.
            assert true == invar1(state1); // one case eliminated.
            assert true == (state2 == iostate(cons(ioaction({c}), iostate_to_list(state1)))); // second case eliminated.
            assert true == ((state2 == iostate(cons(ioaction({c}), iostate_to_list(state1)))) || state2 == state1 ); // third case eliminated.
            assert true == guarantee(state1, state2); // conclusion.
            
            remove_implies_subset(k_time_pairs_old, pair(k_t1, t1));
            assert true == invar2(state2);
            
            distinct_mem_remove(pair(k_t1,t1), k_time_pairs_old);
            assert (!mem(pair(k_t1, t1), remove(pair(k_t1, t1), k_time_pairs_old))); // This is because the k numbers are unique in the ghostlist.
            invar_state1_impl_invar_state2(k_time_pairs_old, remove(pair(k_t1, t1), k_time_pairs_old), pair(k_t1, t1));
            }
            @*/

        //@ assert (true == forall(remove( pair(k_t1, t1), k_time_pairs_old), (invar_applies)(state2))); // End Proof. (1).
        
        //@ assert true == invar_applies(state2, pair(k_t2, t2)); // (2)
        //@ assert k_time_pairs_new == append(remove(pair(k_t1,t1), k_time_pairs_old), {pair(k_t2,t2)});
        //@ forall_append(remove(pair(k_t1,t1), k_time_pairs_old), {pair(k_t2,t2)}, (invar_applies)(state2));
        //@ assert (true == forall(k_time_pairs_new, (invar_applies)(state2)));  // union of (1) and (2).
        
    
    //@ assert true == forall(k_time_pairs_new, (invar_applies)(state2)); // End PROOF.
    
    // PROOF
        /*@{
        
        predicate helperpred() =
            [_]is_forall_t<quadruple<pair<int, time>, pair<int, time>, iostate, iostate > >(?forall_guar_rely2)
            &*& true == forall_guar_rely2((guarantee_preserve_rely)(k_time_pairs_old));
        
        // guarantee_preserve_rely is true for k_time_pairs old, prove that it is also for k_time_pairs_new.
        lemma void guaranteerelylemma(quadruple<pair<int, time>, pair<int, time>, iostate, iostate > quadruple)
        requires helperpred();
        ensures helperpred() &*& true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
        {
            open helperpred();
            close helperpred();
            assert [_]is_forall_t<quadruple<pair<int, time>, pair<int, time>, iostate, iostate > >(?forall_guar_rely2);
            assert true == forall_guar_rely2((guarantee_preserve_rely)(k_time_pairs_old));
            pair<int, time> ktime1 = quadruple1(quadruple);
            pair<int, time> ktime2 = quadruple2(quadruple);
            iostate sigma1 = quadruple3(quadruple);
            iostate sigma2 = quadruple4(quadruple);
            
            forall_t_elim(forall_guar_rely2, (guarantee_preserve_rely)(k_time_pairs_old), quadruple);
            
            if (ktime1 != pair(k_t2, t2) && ktime2 != pair(k_t2, t2)){
                assert true == guarantee_preserve_rely(k_time_pairs_old, quadruple);
                assert ! mem(ktime1, k_time_pairs_old) // this assert is body of prev line
                    || ! mem(ktime2, k_time_pairs_old)
                    || ! (ktime1 != ktime2)
                    || ! (guarantee_of_time(snd(ktime1))) (sigma1, sigma2)
                    || (rely_of_time(snd(ktime2))) (sigma1, sigma2);
                
                
                if (! mem(ktime1, k_time_pairs_old)){
                    neq_mem_remove(ktime1, pair(k_t1, t1), k_time_pairs_old);
                }
                if (! mem(ktime2, k_time_pairs_old)){
                    neq_mem_remove(ktime2, pair(k_t1, t1), k_time_pairs_old);
                }
                
                assert ! mem(ktime1, k_time_pairs_new) // this assert is body of next line
                    || ! mem(ktime2, k_time_pairs_new)
                    || ! (ktime1 != ktime2)
                    || ! (guarantee_of_time(snd(ktime1))) (sigma1, sigma2)
                    || (rely_of_time(snd(ktime2))) (sigma1, sigma2);
                assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
            }else if (ktime1 == ktime2){
            }else if (ktime1 == pair(k_t2, t2)){
                forall_t_elim(forall_guar_rely2, (guarantee_preserve_rely)(k_time_pairs_old), quadruple(pair(k_t1, t1), ktime2, sigma1, sigma2));
                
                assert true == guarantee_preserve_rely(k_time_pairs_old, quadruple(pair(k_t1, t1), ktime2, sigma1, sigma2)); // obtained from prev  line
                assert ! mem(pair(k_t1, t1), k_time_pairs_old) // this assert is body of prev line. // case 1 of t1,ktime2
                    || ! mem(ktime2, k_time_pairs_old) // case 2 of t1,ktime2
                    || ! (pair(k_t1, t1) != ktime2) // case 3 of t1,ktime2
                    || ! (guarantee_of_time(t1)) (sigma1, sigma2) // case4 of t1,ktime2
                    || (rely_of_time(snd(ktime2))) (sigma1, sigma2); // case 5 of t1,ktime2
                    
                if (!mem(pair(k_t1, t1), k_time_pairs_old)){            // case 1 of t1,ktime2
                    assert false;
                    assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
                }else if (!mem(ktime2, k_time_pairs_old)){               // case 2 of t1,ktime2
                    assert ktime2 != pair(k_t2, t2); // (1)
                    assert ktime2 != pair(k_t1, t1); // (2)
                    assert k_time_pairs_new == append(remove( pair(k_t1, t1), k_time_pairs_old ), cons(pair(k_t2, t2), nil)); // (3)
                    
                    assert (!mem(ktime2, k_time_pairs_old));
                    neq_mem_remove(ktime2, pair(k_t1, t1), k_time_pairs_old);
                    assert (!mem(ktime2, remove( pair(k_t1, t1), k_time_pairs_old )));
                    
                    assert !mem(ktime2, k_time_pairs_old); // (4)
                    assert (!mem(ktime2, k_time_pairs_new)); // follows by combining (1),(2),(3),(4)
                    assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
                }else if (!(pair(k_t1, t1) != ktime2)){                // case 3 of t1,ktime2
                    assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
                } else if (! (guarantee_of_time(t1)) (sigma1, sigma2)){ // case 4 of t1,ktime2
                    assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
                } else{ // case 5.
                }
                assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
            }else if (ktime2 == pair(k_t2, t2)){
                forall_t_elim(forall_guar_rely2, (guarantee_preserve_rely)(k_time_pairs_old), quadruple(ktime1, pair(k_t2, t2), sigma1, sigma2));
                
                assert true == guarantee_preserve_rely(k_time_pairs_old, quadruple(ktime1, pair(k_t2, t2), sigma1, sigma2)); // obtained from prev  line
                assert ! mem(ktime1, k_time_pairs_old) // this assert is body of prev line. // case 1 of t1,ktime2
                    || ! mem(pair(k_t2, t2), k_time_pairs_old) // case 2 of t1,ktime2
                    || ! (ktime1 != pair(k_t2, t2)) // case 3 of t1,ktime2
                    || ! (guarantee_of_time(snd(ktime1))) (sigma1, sigma2) // case4 of t1,ktime2
                    || (rely_of_time(t2)) (sigma1, sigma2); // case 5 of t1,ktime2
                    
                if (! mem(ktime1, k_time_pairs_old)){            // case 1 of t1,ktime2
                    assert k_time_pairs_new == append(remove( pair(k_t1, t1), k_time_pairs_old ), cons(pair(k_t2, t2), nil));
                    assert ktime1 != pair(k_t2, t2);
                    
                    assert (!mem(ktime1, k_time_pairs_old));
                    neq_mem_remove(ktime1, pair(k_t1, t1), k_time_pairs_old);
                    assert (!mem(ktime1, remove( pair(k_t1, t1), k_time_pairs_old )));
                    
                    assert ( ! mem(ktime1, k_time_pairs_new)); // Combine above.
                    assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
                }else if (! mem(pair(k_t2, t2), k_time_pairs_old)){               // case 2 of t1,ktime2
                    
                    forall_t_elim(forall_guar_rely2, (guarantee_preserve_rely)(k_time_pairs_old), quadruple(ktime1, pair(k_t1, t1), sigma1, sigma2));
                    assert true == guarantee_preserve_rely(k_time_pairs_old, quadruple(ktime1, pair(k_t1, t1), sigma1, sigma2)); // called "ktime1, t1"
                    assert ! mem(ktime1, k_time_pairs_old) // case 1 of ktime1, t1
                        || ! mem(pair(k_t1, t1), k_time_pairs_old)
                        || ! (ktime1!= pair(k_t1,t1))
                        || ! (guarantee_of_time(snd(ktime1))) (sigma1, sigma2)
                        || (rely_of_time(snd(pair(k_t1, t1)))) (sigma1, sigma2);
                    
                    if (mem(ktime1, k_time_pairs_old)){
                        assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
                    }else if (mem(pair(k_t1, t1), k_time_pairs_old)){
                        assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
                    }else if (ktime1!= pair(k_t1,t1)){
                        assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
                    }else if (! (guarantee_of_time(snd(ktime1))) (sigma1, sigma2)){
                        assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
                    }else if ((rely_of_time(snd(pair(k_t1, t1)))) (sigma1, sigma2)){
                        assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
                    }else{
                        assert false; // running out of cases.
                    }
                    
                    // TODO: in this case we do something else than in the other place where we do the analogue... huh?
                    
                    
                }else if (! (ktime1 != pair(k_t2, t2))){                // case 3 of t1,ktime2
                    assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
                } else if (! (guarantee_of_time(snd(ktime1))) (sigma1, sigma2)){ // case 4 of t1,ktime2
                    assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
                } else{ // case 5.
                }
                assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
                
            }else{
                assert true == guarantee_preserve_rely(k_time_pairs_new, quadruple);
            }
            
        }
        
        produce_lemma_function_pointer_chunk(guaranteerelylemma) :
                    forall_proof_t<quadruple<pair<int, time>, pair<int, time>, iostate, iostate > >((guarantee_preserve_rely)(k_time_pairs_new), helperpred)(arg)
                {
                    
                    get_forall_t<quadruple<pair<int, time>, pair<int, time>, iostate, iostate > > ();
                    call();
                }
                {
                    close helperpred();
                    apply_forall_proof(guaranteerelylemma, (guarantee_preserve_rely)(k_time_pairs_new), helperpred);
                    open helperpred();
                }
        
        
        
        }@*/
        
    //@ assert true == forall_guar_rely((guarantee_preserve_rely)(k_time_pairs_new));
    
    
    // PROOF: rely preserve invar
        /*@{
        // rely_preserve_invar is true for k_time_pairs old, prove that it is also for k_time_pairs_new.
        lemma void relyinvarlemma(pair<pair<int, time>,  pair<iostate, iostate > > pair)
        requires helperpred2();
        ensures helperpred2() &*& true == rely_preserve_invar(k_time_pairs_new, pair);
        {
        
            open helperpred2();
            assert [_]is_forall_t< pair< pair<int,time>, pair<iostate, iostate > > >(?forall_ktimesigmasigma2);
            assert [_]is_forall_t<pair<iostate, iostate > >(?forall_sigmapair2);
        
            pair<int, time> ktime = fst(pair);
            pair<iostate, iostate > sigmapair = snd(pair);  
                
            if (!mem(ktime, k_time_pairs_new)){
                assert true == rely_preserve_invar(k_time_pairs_new, pair);
            }else{
                if (ktime == pair(k_t2, t2)){
                    assert true == forall_sigmapair2((invar_closed_under_rely)(t2));
                    //->
                        forall_t_elim(forall_sigmapair2, (invar_closed_under_rely)(t2), sigmapair);
                    assert true == invar_closed_under_rely(t2, sigmapair);
                
                    assert true == rely_preserve_invar(k_time_pairs_new, pair);
                }else{
                    
                    //->
                        forall_t_elim(forall_ktimesigmasigma2, (rely_preserve_invar)(k_time_pairs_old), pair);
                    assert true == rely_preserve_invar(k_time_pairs_old, pair);
                    assert !mem(fst(pair), k_time_pairs_old) || invar_closed_under_rely(snd(fst(pair)), snd(pair)); // body of prev line
                    if (!mem(fst(pair), k_time_pairs_old)){
                        
                        if (!mem(fst(pair), k_time_pairs_new)){
                            assert true == rely_preserve_invar(k_time_pairs_new, pair);
                        }else{
                            assert ktime == fst(pair);
                            assert !mem(ktime, k_time_pairs_old);
                            assert true==mem(ktime, k_time_pairs_new);
                            
                            assert k_time_pairs_new == append(remove( pair(k_t1, t1), k_time_pairs_old ), cons(pair(k_t2, t2), nil));
                            neq_mem_remove(ktime, pair(k_t1,t1), k_time_pairs_old);
                            
                            assert !mem(ktime, remove( pair(k_t1, t1), k_time_pairs_old )); // (1)
                            assert true==mem(ktime, k_time_pairs_new) && ktime != pair(k_t2,t2) && ktime != pair(k_t1,t1) && !mem(ktime, k_time_pairs_old); // (2)
                            
                            assert(ktime == pair(k_t2, t2)); // combine (1) and (2).
                            assert true == rely_preserve_invar(k_time_pairs_new, pair);
                        }
                    }else{
                        assert true == rely_preserve_invar(k_time_pairs_new, pair);
                    }
                }
            }
            
            close helperpred2();
        }
        
        predicate helperpred2() = 
            [_]is_forall_t< pair< pair<int,time>, pair<iostate, iostate > > >(?forall_ktimesigmasigma2)
            &*& true == forall_ktimesigmasigma2((rely_preserve_invar)(k_time_pairs_old))
            
            &*& [_]is_forall_t<pair<iostate, iostate > >(?forall_sigmapair2)
            &*& true == forall_sigmapair2((invar_closed_under_rely)(t2))
       ;
        
        produce_lemma_function_pointer_chunk(relyinvarlemma) :
                    forall_proof_t<pair< pair<int,time>, pair<iostate, iostate > > >((rely_preserve_invar)(k_time_pairs_new), helperpred2)(arg)
                {
                    
                    get_forall_t<triple<pair<int, time>, iostate, iostate > > ();
                    call();
                }
                {
                    close helperpred2();
                    apply_forall_proof(relyinvarlemma, (rely_preserve_invar)(k_time_pairs_new), helperpred2);
                    open helperpred2();
                } 
                
        }@*/
        
    //@ assert true == forall_ktimesigmasigma((rely_preserve_invar)(k_time_pairs_new)); // End proof.
    
    //@ close iothreads(ghost_list_id, iostate({ioaction({c})}));
    //@ close time(ghost_list_id, t2);
    //@ close syscall_iostate(iostate({ioaction({c})}));
    //@ close iostate(ghost_list_id, iostate({ioaction({c})}));
}

