/**
 * !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
 * If you are looking for examples of I/O, you are at the wrong file.
 * !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
 *
 * See syscall_memory.c to read what this is about.
 *
 * Launch with: vfide -I . io_lemma_impl.c
 */
 
/*
 * The other part is in io_pred_bodies.gh
 */

//@ #include <io/io.gh>
//@ #include <quantifiers.gh>
//@ #include <io/io_pred_bodies.gh>

/*@

lemma void or_keeps_reflexivity(fixpoint(iostate, iostate, bool) transition1,
    fixpoint(iostate, iostate, bool) transition2)
requires
    [_]is_forall_t<iostate >(?forall_singleton)
    &*& forall_singleton((reflexive)(transition1)) == true
    &*& forall_singleton((reflexive)(transition2)) == true;
ensures
    forall_singleton(
        (reflexive)(
            (transition_or)(transition1, transition2)
        )
    ) == true;
{
    if (!forall_singleton(
        (reflexive)(
            (transition_or)(transition1, transition2)
        )
    )){
        iostate sigma = not_forall_t(
            forall_singleton,
            (reflexive)(
                (transition_or)(transition1, transition2)
            )
        );
        forall_t_elim(
            forall_singleton,
            (reflexive)(transition1),
            sigma
        );
    }
}

lemma void split()
requires split(?t1, ?t2, ?t3) &*& time(?ghost_list_id, t1) &*& iothreads(ghost_list_id, ?state);
ensures time(ghost_list_id, t2) &*& time(ghost_list_id, t3) &*& iothreads(ghost_list_id, state);
{
    open split(t1, t2, t3);
    open time(?t1_id, t1);
    open iothreads(ghost_list_id, state);
    open iothreads_pure(_, _);
    assert cooked_ghost_list(ghost_list_id, ?n_old, ?k_time_pairs_old);
    assert cooked_ghost_list_member_handle(ghost_list_id, ?k_t1, t1);
    cooked_ghost_list_match(ghost_list_id, k_t1);
    cooked_ghost_list_remove(ghost_list_id, k_t1);
    cooked_ghost_list_add(ghost_list_id, t2);
    cooked_ghost_list_add(ghost_list_id, t3);
    assert [_]is_forall_t<triple<iostate,iostate,iostate > >(?forall_triple);
    or_keeps_reflexivity(guarantee_of_time(t3), rely_of_time(t1));
    or_keeps_reflexivity(guarantee_of_time(t2), rely_of_time(t1));
    close time(ghost_list_id, t2);
    close time(ghost_list_id, t3);
    
    assert cooked_ghost_list(ghost_list_id, ?n_new, ?k_time_pairs_new);
    list<pair<int, time> > k_time_pairs_new1 = remove(pair(k_t1, t1), k_time_pairs_old);
    list<pair<int, time> > k_time_pairs_new2 = append(k_time_pairs_new1, {pair(n_old, t2)});
    assert k_time_pairs_new  == append(k_time_pairs_new2, {pair(n_old+1, t3)});
    
    forall_remove(k_time_pairs_old, (invar_applies)(state), pair(k_t1, t1));
    assert true==forall(k_time_pairs_new1, (invar_applies)(state));
    forall_append(
        k_time_pairs_new1,
        {pair(n_old, t2)},
        (invar_applies)(state)
    );
    forall_elim(k_time_pairs_old, (invar_applies)(state), pair(k_t1, t1));
    
    int k_t2 = n_old;
    int k_t3 = n_old+1;
    
    assert true==invar_applies(state, pair(k_t1, t1));
        
    if (!forall(k_time_pairs_new, (invar_applies)(state))){
    
        assert [_]is_forall_t<iostate >(?forall_singleton);
        forall_t_elim(forall_singleton, (reflexive)(rely_of_time(t3)), state);
        forall_t_elim(forall_singleton, (reflexive)(rely_of_time(t2)), state);
        
        assert [_]is_forall_t<pair<iostate, iostate > >(?forall_sigmapair);
        forall_t_elim(forall_sigmapair, (invar_transition_eq_invar)(invar_of_time(t1), rely_of_time(t2), invar_of_time(t2)), pair(state,state));
        forall_t_elim(forall_sigmapair, (invar_transition_eq_invar)(invar_of_time(t1), rely_of_time(t3), invar_of_time(t3)), pair(state,state));
        
        assert true == forall({pair(k_t2, t2)}, (invar_applies)(state));
        assert true == forall({pair(k_t3, t3)}, (invar_applies)(state));
        assert true == forall(k_time_pairs_new2, (invar_applies)(state));

    
        forall_append(
            append(remove(pair(k_t1, t1), k_time_pairs_old), {pair(n_old, t2)}),
            {pair(n_old+1, t3)},
            (invar_applies)(state)
        );
        
        assert false;
    }
    
    distinct_mem_remove(pair(k_t1,t1), k_time_pairs_old);
    assert !mem(pair(k_t1,t1), k_time_pairs_new1);
    mem_append(pair(k_t1,t1), k_time_pairs_old, {pair(k_t2, t2)});
    assert !mem(pair(k_t1, t1), k_time_pairs_new1);
    
    assert [_]is_forall_t< quadruple< pair<int,time>, pair<int, time>, iostate, iostate > >(?forall_guar_rely);
    if (!forall_guar_rely((guarantee_preserve_rely)(k_time_pairs_new))){
        quadruple< pair<int,time>, pair<int, time>, iostate, iostate > quad = not_forall_t(forall_guar_rely, (guarantee_preserve_rely)(k_time_pairs_new));
        pair<int, time> time1 = quadruple1(quad);
        pair<int, time> time2 = quadruple2(quad);
        iostate sigma1 = quadruple3(quad);
        iostate sigma2 = quadruple4(quad);
        
        if (! mem(time1, k_time_pairs_old)){
            neq_mem_remove(time1, pair(k_t1, t1), k_time_pairs_old);
        }
        if (! mem(time2, k_time_pairs_old)){
            neq_mem_remove(time2, pair(k_t1, t1), k_time_pairs_old);
        }
        
        if (time1 != pair(k_t2, t2) && time2 != pair(k_t2, t2) && time1 != pair(k_t3, t3) && time2 != pair(k_t3, t3)){
            forall_t_elim(forall_guar_rely, (guarantee_preserve_rely)(k_time_pairs_old), quad);
            
            assert false;
        }else{          
            quadruple< pair<int,time>, pair<int, time>, iostate, iostate > quad_t1_time1 =
                quadruple(quadruple1(quad), pair(k_t1, t1), quadruple3(quad), quadruple4(quad));
            quadruple< pair<int,time>, pair<int, time>, iostate, iostate > quad_t1_time2 =
                quadruple(pair(k_t1, t1), quadruple2(quad), quadruple3(quad), quadruple4(quad));
            forall_t_elim(forall_guar_rely, (guarantee_preserve_rely)(k_time_pairs_old), quad_t1_time2);
            forall_t_elim(forall_guar_rely, (guarantee_preserve_rely)(k_time_pairs_old), quad_t1_time1);
            
            assert [_]is_forall_t<pair<iostate, iostate > >(?forall_sigmapair);
            forall_t_elim(
                forall_sigmapair,
                (arrows_transition_transition)(
                    (transition_or)(guarantee_of_time(t3), rely_of_time(t1)),
                    rely_of_time(t2)
                ),
                pair(sigma1, sigma2)
            );
            forall_t_elim(
                forall_sigmapair,
                (arrows_transition_transition)(
                    (transition_or)(guarantee_of_time(t2), rely_of_time(t1)),
                    rely_of_time(t3)
                ),
                pair(sigma1, sigma2)
            );
            
            assert true==mem(quadruple1(quad), k_time_pairs_new);
            assert true==mem(quadruple2(quad), k_time_pairs_new);
            assert quadruple1(quad) != quadruple2(quad);
            assert true==
                (guarantee_of_time(snd(quadruple1(quad))))
                (quadruple3(quad), quadruple4(quad));
            assert true==(rely_of_time(snd(quadruple2(quad)))) (quadruple3(quad), quadruple4(quad));
            
            assert false;
        }
        assert false;
    }
    
    assert [_]is_forall_t< pair< pair<int,time>, pair<iostate, iostate > > >(?forall_ktimesigmasigma);
    if (!forall_ktimesigmasigma((rely_preserve_invar)(k_time_pairs_new))){
        pair< pair<int,time>, pair<iostate, iostate > > ktimesigmasigma = not_forall_t(forall_ktimesigmasigma, (rely_preserve_invar)(k_time_pairs_new));
        pair<int, time> ktime = fst(ktimesigmasigma);
        iostate sigma1 = fst(snd(ktimesigmasigma));
        iostate sigma2 = snd(snd(ktimesigmasigma));
        
        assert [_]is_forall_t<pair<iostate, iostate > >(?forall_sigmapair);
        if (ktime == pair(k_t2, t2)){
            forall_t_elim(forall_sigmapair, (invar_transition_eq_invar)(invar_of_time(t1), rely_of_time(t2), invar_of_time(t2)), pair(sigma1, sigma2));
            assert false;
        }else if (ktime == pair(k_t3, t3)){
            forall_t_elim(forall_sigmapair, (invar_transition_eq_invar)(invar_of_time(t1), rely_of_time(t3), invar_of_time(t3)), pair(sigma1, sigma2));
            assert false;
        }else if (ktime == pair(k_t1, t1)){
            assert (!mem(pair(k_t1,t1), k_time_pairs_new1));
            assert false;
        }else{
            if (! mem(ktime, k_time_pairs_old)){
                neq_mem_remove(ktime, pair(k_t1, t1), k_time_pairs_old);
                assert !mem(ktim, k_time_pairs_new); // because prev line.
                assert false;
            }else{
                forall_t_elim(forall_ktimesigmasigma, (rely_preserve_invar)(k_time_pairs_old), ktimesigmasigma);
                assert false;
            }
        }
        assert false;
    }
    
    close iothreads_pure(k_time_pairs_new, state);
    leak iothreads_pure(k_time_pairs_new, state);
    close iothreads(ghost_list_id, state);
}

lemma void join()
requires join(?t1, ?t2, ?t3) &*& time(?ghost_list_id, t1) &*& time(ghost_list_id, t2) &*& iothreads(ghost_list_id, ?state);
ensures time(ghost_list_id, t3) &*& iothreads(ghost_list_id, state);
{
    open join(t1, t2, t3);
    open time(ghost_list_id, t1);
    open time(ghost_list_id, t2);
    open iothreads(ghost_list_id,state);
    open iothreads_pure(_, _);
    
    assert cooked_ghost_list_member_handle(_, ?k_t1, t1) &*& cooked_ghost_list_member_handle(_, ?k_t2, t2);
    assert cooked_ghost_list(_, ?n, ?k_time_pairs_old);
    
    // add t3.
    cooked_ghost_list_add(ghost_list_id, t3);
    assert cooked_ghost_list(_, _, ?k_time_pairs_add3);
    assert k_time_pairs_add3 == append(k_time_pairs_old, {pair(n,t3)});
    int k_t3 = n;
    
    // Obtain mem(pair(k_t1), k_time_pairs_add1).
    cooked_ghost_list_match(ghost_list_id, k_t1);
    cooked_ghost_list_match(ghost_list_id, k_t2);
    
    cooked_ghost_list_remove(ghost_list_id, k_t1);
    assert cooked_ghost_list(_, _, ?k_time_pairs_rem1);
    assert k_time_pairs_rem1 == remove(pair(k_t1,t1), k_time_pairs_add3);
    distinct_mem_remove(pair(k_t1,t1), k_time_pairs_add3);
    assert !mem(pair(k_t1,t1), k_time_pairs_rem1);
    
    cooked_ghost_list_remove(ghost_list_id, k_t2);
    assert cooked_ghost_list(_, _, ?k_time_pairs_rem2);
    assert k_time_pairs_rem2 == remove(pair(k_t2,t2), k_time_pairs_rem1);
    distinct_mem_remove(pair(k_t2,t2), k_time_pairs_rem1);
    assert !mem(pair(k_t2,t2), k_time_pairs_rem2);
    
    if (pair(k_t1,t1) != pair(k_t2,t2)){
        neq_mem_remove(pair(k_t1,t1), pair(k_t2,t2), k_time_pairs_rem1);
    }else{
        // Actually can't happen but VeriFast doesn't know that.
        distinct_mem_remove(pair(k_t1,t1), k_time_pairs_rem1);
    }
    assert !mem(pair(k_t1,t1), k_time_pairs_rem2);
        
    list<pair<int, time> > k_time_pairs_new = k_time_pairs_rem2;
        
    // TODO: introduce helper lemma "and_keeps_transitivity"?
    assert [_]is_forall_t<triple<iostate,iostate,iostate > >(?forall_triple);
    if (!forall_triple((transitive)(guarantee_of_time(t3)))){
        triple<iostate,iostate,iostate > triple = not_forall_t(forall_triple, (transitive)(guarantee_of_time(t3)));
        forall_t_elim(forall_triple, (transitive)(guarantee_of_time(t1)), triple);
        forall_t_elim(forall_triple, (transitive)(guarantee_of_time(t2)), triple);
    }
    if (!forall_triple((transitive)(rely_of_time(t3)))){
        triple<iostate,iostate,iostate > triple = not_forall_t(forall_triple, (transitive)(rely_of_time(t3)));
        forall_t_elim(forall_triple, (transitive)(rely_of_time(t1)), triple);
        forall_t_elim(forall_triple, (transitive)(rely_of_time(t2)), triple);
    }
    
    assert [_]is_forall_t<iostate >(?forall_singleton);
    if (!forall_singleton((reflexive)(guarantee_of_time(t3)))){
        iostate sigma = not_forall_t(forall_singleton, (reflexive)(guarantee_of_time(t3)));
        forall_t_elim(forall_singleton, (reflexive)(guarantee_of_time(t1)), sigma);
        forall_t_elim(forall_singleton, (reflexive)(guarantee_of_time(t2)), sigma);
    }
    if (!forall_singleton((reflexive)(rely_of_time(t3)))){
        iostate sigma = not_forall_t(forall_singleton, (reflexive)(rely_of_time(t3)));
        forall_t_elim(forall_singleton, (reflexive)(rely_of_time(t1)), sigma);
        forall_t_elim(forall_singleton, (reflexive)(rely_of_time(t2)), sigma);
    }
    
    close time(ghost_list_id, t3);
    
    if (!forall(k_time_pairs_new, (invar_applies)(state))){ // TODO: this is very similar to split(). Merge to helper lemmas?
        pair<int, time > ktime = not_forall(k_time_pairs_new, (invar_applies)(state));
        
        if (ktime == pair(k_t1, t1)){
            assert false;
        }else if (ktime == pair(k_t2, t2)){
            assert false;
        }else if (ktime == pair(k_t3, t3)){
            forall_elim(k_time_pairs_old, (invar_applies)(state), pair(k_t1, t1));
            forall_elim(k_time_pairs_old, (invar_applies)(state), pair(k_t2, t2));
            assert false;
        }else{
            neq_mem_remove(ktime, pair(k_t2,t2), k_time_pairs_rem1);
            neq_mem_remove(ktime, pair(k_t1,t1), k_time_pairs_add3);
            mem_append(ktime, k_time_pairs_old, {pair(k_t3, t3)});
            assert true==mem(ktime, k_time_pairs_old);
            
            forall_elim(k_time_pairs_old, (invar_applies)(state), ktime);
            assert false;
        }
    
        assert false;
    }
    
    assert [_]is_forall_t< quadruple< pair<int,time>, pair<int, time>, iostate, iostate > >(?forall_guar_rely);
    if (!forall_guar_rely((guarantee_preserve_rely)(k_time_pairs_new))){
        quadruple< pair<int,time>, pair<int, time>, iostate, iostate > quad = not_forall_t(forall_guar_rely, (guarantee_preserve_rely)(k_time_pairs_new));
        
        if (quadruple1(quad) == pair(k_t1,t1) || quadruple1(quad) == pair(k_t2,t2) || quadruple2(quad) == pair(k_t1,t1) || quadruple2(quad) == pair(k_t2,t2)){
            assert false;
        }else if (quadruple1(quad) == pair(k_t3,t3) && quadruple2(quad) == pair(k_t3,t3)){
            assert false;
        }else{
            neq_mem_remove(quadruple2(quad), pair(k_t2,t2), k_time_pairs_rem1);
            neq_mem_remove(quadruple2(quad), pair(k_t1,t1), k_time_pairs_add3);
            mem_append(quadruple2(quad), k_time_pairs_old, {pair(k_t3, t3)});
            
            neq_mem_remove(quadruple1(quad), pair(k_t2,t2), k_time_pairs_rem1);
            neq_mem_remove(quadruple1(quad), pair(k_t1,t1), k_time_pairs_add3);
            mem_append(quadruple1(quad), k_time_pairs_old, {pair(k_t3, t3)});
            
            if (quadruple1(quad) == pair(k_t3,t3)){
                assert true==mem(quadruple2(quad), k_time_pairs_old);
            
                forall_t_elim(forall_guar_rely, (guarantee_preserve_rely)(k_time_pairs_old), quadruple(pair(k_t1,t1), quadruple2(quad), quadruple3(quad), quadruple4(quad)));           
                assert false;
            }else if (quadruple2(quad) == pair(k_t3,t3)){
                assert true==mem(quadruple1(quad), k_time_pairs_old);
            
                forall_t_elim(forall_guar_rely, (guarantee_preserve_rely)(k_time_pairs_old), quadruple(quadruple1(quad), pair(k_t1,t1), quadruple3(quad), quadruple4(quad)));           
                forall_t_elim(forall_guar_rely, (guarantee_preserve_rely)(k_time_pairs_old), quadruple(quadruple1(quad), pair(k_t2,t2), quadruple3(quad), quadruple4(quad)));           
                assert false;
            }else{
                assert true==mem(quadruple1(quad), k_time_pairs_old);
                assert true==mem(quadruple2(quad), k_time_pairs_old);
                
                forall_t_elim(forall_guar_rely, (guarantee_preserve_rely)(k_time_pairs_old), quadruple(quadruple1(quad), quadruple2(quad), quadruple3(quad), quadruple4(quad)));            
                assert false;
            }
        }
        
        assert false;
    }

    assert [_]is_forall_t< pair< pair<int,time>, pair<iostate, iostate > > >(?forall_ktimesigmasigma);
    if (!forall_ktimesigmasigma((rely_preserve_invar)(k_time_pairs_new))){
        pair< pair<int,time>, pair<iostate, iostate > > pair = not_forall_t(forall_ktimesigmasigma, (rely_preserve_invar)(k_time_pairs_new));
        
        neq_mem_remove(fst(pair), pair(k_t2,t2), k_time_pairs_rem1);
        neq_mem_remove(fst(pair), pair(k_t1,t1), k_time_pairs_add3);
        mem_append(fst(pair), k_time_pairs_old, {pair(k_t3, t3)});
        
        if (fst(pair) == pair(k_t1, t1) || fst(pair) == pair(k_t2, t2) ){
            assert false;
        }else if (fst(pair) == pair(k_t3, t3)){
            forall_t_elim(forall_ktimesigmasigma, (rely_preserve_invar)(k_time_pairs_old), pair(pair(k_t1, t1), snd(pair)));
            forall_t_elim(forall_ktimesigmasigma, (rely_preserve_invar)(k_time_pairs_old), pair(pair(k_t2, t2), snd(pair)));
            assert false;
        }else{
            assert true==mem(fst(pair), k_time_pairs_new);
            assert (true==mem(fst(pair), k_time_pairs_old));
            forall_t_elim(forall_ktimesigmasigma, (rely_preserve_invar)(k_time_pairs_old), pair);
            assert false;
        }
    }
    
    close iothreads_pure(k_time_pairs_new, state);
    leak iothreads_pure(k_time_pairs_new, state);
    close iothreads(ghost_list_id, state);
}
@*/
