#include <stdlib.h>
#include "mutexes.h"
#include "semas.h"
#include "queues.h"
//@ #include "ghost_counters.gh"
//@ #include "splittable_counting.gh"
#include "channels.h"

/*

Deadlock-preventing specification approach based on [K.R.M. Leino, P. Mueller, J. Smans. Deadlock-free channels and locks. ESOP 2010].

This is not the most general possible specification. It is a tradeoff between generality and simplicity.
A more general specification would require a credit only at the point of blocking.
This spec does not support e.g. the case where you know that any one of two channels may block, but they will not both block.

*/

struct channel {
    mutex mutex;
    sema sema;
    queue queue;
    //@ real spaceFrac;
    //@ level level;
    //@ int counterId;
    //@ int countingId;
    //@ int creditObject;
    //@ predicate(list<void *>) inv_;
    //@ int emptinessCountingId;
    //@ int emptinessToken;
};

/*@

predicate_ctor emptiness_ticket(channel channel, int emptinessCountingId)() =
    counting_ticket(emptinessCountingId, ?frac) &*& [frac/2]channel->emptinessToken |-> 0 &*& 0 < frac;

predicate_ctor channel_mutex_inv(channel channel, queue queue, predicate(list<void *>) inv, int counterId, int emptinessCountingId)() =
    queue(queue, ?elems) &*& inv(elems) &*& n_times(length(elems), emptiness_ticket(channel, emptinessCountingId)) &*&
    ghost_counter(counterId, length(elems));

predicate_ctor channel_sema_inv(channel channel)() =
    [?frac]channel(channel, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, ?sema, ?counterId, ?countingId, ?emptinessCountingId) &*& 0 < frac &*&
    counting_ticket(countingId, 2*frac) &*&
    ghost_counter_ticket(counterId);

predicate_ctor channel_(channel channel)(;) = [1/2]channel(channel, _, _, _, _, _, _, _, _, _, _);

predicate channel(channel channel; int space, int termScope, real spaceFrac, level level, int creditObject, predicate(list<void *>) inv, sema sema, int counterId, int countingId, int emptinessCountingId) =
    channel->mutex |-> ?mutex &*&
    channel->sema |-> sema &*&
    channel->queue |-> ?queue &*&
    channel->level |-> level &*&
    channel->counterId |-> counterId &*&
    channel->countingId |-> countingId &*&
    channel->creditObject |-> creditObject &*&
    channel->inv_ |-> inv &*&
    channel->emptinessCountingId |-> emptinessCountingId &*&
    malloc_block_channel(channel) &*&
    channel->spaceFrac |-> spaceFrac &*& 0 < spaceFrac &*&
    mutex(mutex, space, termScope, spaceFrac/2, ?mutexLevel, channel_mutex_inv(channel, queue, inv, counterId, emptinessCountingId)) &*&
    level_below(mutexLevel, level) == true;

predicate_ctor channel_emptinessToken_(channel channel)(;) = [1/2]channel->emptinessToken |-> 0;

predicate channel_handle(channel channel, real frac, int space, int termScope, real spaceFrac, level level, int creditObject, predicate(list<void *>) inv, int sendTokens) =
    [frac/2]channel(channel, space, termScope, spaceFrac, level, creditObject, inv, ?sema, ?counterId, ?countingId, ?emptinessCountingId) &*& 0 < frac &*&
    [frac/2]channel->emptinessToken |-> 0 &*&
    counting_handle(emptinessCountingId, channel_emptinessToken_(channel), frac, sendTokens) &*&
    counting_handle(countingId, channel_(channel), frac, sendTokens) &*&
    sema_handle(sema, frac, space, termScope, spaceFrac / 2, level, creditObject, channel_sema_inv(channel), sendTokens);

predicate channel_send_token(channel channel, int space, int termScope, level level, int creditObject, predicate(list<void *>) inv) =
    [?frac]channel(channel, space, termScope, ?fs, level, creditObject, inv, ?sema, ?counterId, ?countingId, ?emptinessCountingId) &*&
    counting_ticket(countingId, 2*frac) &*&
    [?frac2]channel->emptinessToken |-> 0 &*&
    counting_ticket(emptinessCountingId, 2*frac2) &*&
    sema_release_token(sema, space, termScope, level, creditObject, channel_sema_inv(channel));

lemma void channel_create_send_token(channel channel)
    nonghost_callers_only
    requires channel_handle(channel, ?f, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, ?sendTokens);
    ensures channel_handle(channel, f, space, termScope, fs, level, creditObject, inv, sendTokens + 1) &*& channel_send_token(channel, space, termScope, level, creditObject, inv);
{
    open channel_handle(channel, f, space, termScope, fs, level, creditObject, inv, sendTokens);
    assert [f/2]channel(channel, space, termScope, fs, level, creditObject, inv, ?sema, ?counterId, ?countingId, ?emptinessCountingId);
    create_counting_ticket(countingId);
    create_counting_ticket(emptinessCountingId);
    sema_create_release_token(sema);
    open channel_(channel)();
    open channel_emptinessToken_(channel)();
    close channel_handle(channel, f, space, termScope, fs, level, creditObject, inv, sendTokens + 1);
    close channel_send_token(channel, space, termScope, level, creditObject, inv);
}

lemma void channel_handle_split(channel channel, real f1, int sendTokens1)
    nonghost_callers_only
    requires channel_handle(channel, ?f, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, ?sendTokens) &*& 0 < f1 &*& f1 < f;
    ensures channel_handle(channel, f1, space, termScope, fs, level, creditObject, inv, sendTokens1) &*& channel_handle(channel, f - f1, space, termScope, fs, level, creditObject, inv, sendTokens - sendTokens1);
{
    open channel_handle(channel, f, space, termScope, fs, level, creditObject, inv, sendTokens);
    assert [f/2]channel(channel, space, termScope, fs, level, creditObject, inv, ?sema, ?counterId, ?countingId, ?emptinessCountingId);
    split_counting_handle(countingId, f1, sendTokens1);
    split_counting_handle(emptinessCountingId, f1, sendTokens1);
    sema_handle_split(sema, f1, sendTokens1);
    close channel_handle(channel, f1, space, termScope, fs, level, creditObject, inv, sendTokens1);
    close channel_handle(channel, f - f1, space, termScope, fs, level, creditObject, inv, sendTokens - sendTokens1);
}

lemma void channel_handle_merge(channel channel)
    nonghost_callers_only
    requires channel_handle(channel, ?f1, ?space1, ?termScope1, ?fs1, ?level1, ?creditObject1, ?inv1, ?sendTokens1) &*& channel_handle(channel, ?f2, ?space2, ?termScope2, ?fs2, ?level2, ?creditObject2, ?inv2, ?sendTokens2);
    ensures channel_handle(channel, f1 + f2, space1, termScope1, fs1, level1, creditObject1, inv1, sendTokens1 + sendTokens2) &*&
        space2 == space1 &*& termScope2 == termScope1 &*& fs2 == fs1 &*& level2 == level1 &*& creditObject2 == creditObject1 &*& inv2 == inv1;
{
    open channel_handle(channel, f1, space1, termScope1, fs1, level1, creditObject1, inv1, sendTokens1);
    open channel_handle(channel, f2, space2, termScope2, fs2, level2, creditObject2, inv2, sendTokens2);
    assert [(f1 + f2)/2]channel(channel, space1, termScope1, fs1, level1, creditObject1, inv1, ?sema, ?counterId, ?countingId, ?emptinessCountingId);
    merge_counting_handle(countingId);
    merge_counting_handle(emptinessCountingId);
    sema_handle_merge(sema);
    close channel_handle(channel, f1 + f2, space1, termScope1, fs1, level1, creditObject1, inv1, sendTokens1 + sendTokens2);
}

@*/

channel create_channel()
    //@ requires exists<real>(?fs) &*& 0 < fs &*& [fs]obligation_space(?space, ?termScope) &*& obspace_credit_object(?creditObject, space, ?level, 0, 0) &*& exists<predicate(list<void *>)>(?inv) &*& inv(nil);
    //@ ensures channel_handle(result, 1, space, termScope, fs, level, creditObject, inv, 0);
    //@ terminates;
{
    //@ open exists(fs);
    //@ open exists(inv);
    channel channel = malloc(sizeof(struct channel));
    if (channel == 0) abort();
    channel->queue = create_queue();
    //@ channel->emptinessToken = 0;
    //@ int counterId = create_ghost_counter();
    //@ int emptinessCountingId = create_counting_handle_id_reservation();
    //@ close channel_emptinessToken_(channel)();
    //@ create_counting_handle(channel_emptinessToken_(channel));
    //@ close n_times(0, emptiness_ticket(channel, emptinessCountingId));
    //@ close channel_mutex_inv(channel, channel->queue, inv, counterId, emptinessCountingId)();
    //@ level mutexLevel = create_level(nil, {level});
    //@ close exists(mutexLevel);
    //@ close exists(channel_mutex_inv(channel, channel->queue, inv, counterId, emptinessCountingId));
    //@ close exists(fs/2);
    channel->mutex = create_mutex();
    //@ close exists(fs/2);
    //@ close exists(channel_sema_inv(channel));
    channel->sema = create_sema();
    //@ channel->counterId = counterId;
    //@ int countingId = create_counting_handle_id_reservation();
    //@ channel->countingId = countingId;
    //@ channel->creditObject = creditObject;
    //@ channel->inv_ = inv;
    //@ channel->emptinessCountingId = emptinessCountingId;
    //@ channel->level = level;
    //@ channel->spaceFrac = fs;
    //@ close channel_(channel)();
    //@ create_counting_handle(channel_(channel));
    //@ close channel_handle(channel, 1, space, termScope, fs, level, creditObject, inv, 0);
    return channel;
}

/*@

lemma void level_all_above_below(list<level> levels, level level1, level level2)
    requires level_below(level2, level1) && level_all_above(levels, level1);
    ensures level_all_above(levels, level2) == true;
{
    switch (levels) {
        case nil:
        case cons(l, ls):
            level_below_transitive(level2, level1, l);
            level_all_above_below(ls, level1, level2);
    }
}

lemma void level_all_above_or_eq_below(list<level> levels, level level1, level level2)
    requires level_below(level2, level1) && level_all_above_or_eq(levels, level1);
    ensures level_all_above(levels, level2) == true;
{
    switch (levels) {
        case nil:
        case cons(l, ls):
            if (l != level1)
                level_below_transitive(level2, level1, l);
            level_all_above_or_eq_below(ls, level1, level2);
    }
}

@*/

void channel_send(channel channel, void *message)
    /*@
    requires
        channel_send_token(channel, ?space, ?termScope, ?level, ?creditObject, ?inv) &*&
        obspace_obligation_set(space, ?obs) &*& level_all_above_or_eq(obs, level) == true &*&
        is_channel_send_ghost_op(?op, inv, message, ?P, ?Q) &*& P()
        &*& exists<bool>(?final) &*&
        final ?
            obs == {level} &*& debit(creditObject) &*& obspace_joinee(space)
            &*& ensures stop_perm(termScope) &*& Q()
        :
            ensures
                obspace_obligation_set(space, obs) &*&
                credit(creditObject) &*& Q();
    @*/
    //@ ensures emp;
    //@ terminates;
{
    //@ open channel_send_token(channel, space, termScope, level, creditObject, inv);
    //@ open [?f]channel(channel, _, _, ?spaceFrac, _, _, _, _, _, _, _);
    //@ assert [_]mutex(_, _, _, _, ?mutexLevel, _);
    //@ level_all_above_or_eq_below(obs, level, mutexLevel);
    mutex_acquire(channel->mutex);
    //@ int emptinessCountingId = channel->emptinessCountingId;
    //@ open channel_mutex_inv(channel, channel->queue, inv, channel->counterId, emptinessCountingId)();
    enqueue(channel->queue, message);
    //@ create_ghost_counter_ticket(channel->counterId);
    //@ op();
    //@ assert n_times(?n, emptiness_ticket(channel, emptinessCountingId));
    //@ close emptiness_ticket(channel, emptinessCountingId)();
    //@ close n_times(n + 1, emptiness_ticket(channel, emptinessCountingId));
    //@ close channel_mutex_inv(channel, channel->queue, inv, channel->counterId, channel->emptinessCountingId)();
    mutex_release(channel->mutex);
    sema sema = channel->sema;
    //@ close channel_sema_inv(channel)();
    sema_release(sema);
    //@ leak is_channel_send_ghost_op(op, inv, message, P, Q);
}

void *channel_receive(channel channel)
    /*@
    requires
        channel_handle(channel, ?f, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, ?sendTokens) &*&
        obspace_obligation_set(space, ?obs) &*& level_all_above(obs, level) == true &*&
        credit(creditObject) &*&
        is_channel_receive_ghost_op(?op, inv, ?P, ?Q) &*& P();
    @*/
    /*@
    ensures
        channel_handle(channel, f, space, termScope, fs, level, creditObject, inv, sendTokens - 1) &*&
        obspace_obligation_set(space, obs) &*&
        Q(result);
    @*/
    //@ terminates;
{
    //@ open channel_handle(channel, f, space, termScope, fs, level, creditObject, inv, sendTokens);
    sema_acquire(channel->sema);
    //@ open channel_sema_inv(channel)();
    //@ open channel(channel, _, _, _, _, _, _, _, _, ?countingId, ?emptinessCountingId);
    //@ assert [_]mutex(_, _, _, _, ?mutexLevel, _);
    //@ level_all_above_below(obs, level, mutexLevel);
    mutex_acquire(channel->mutex);
    //@ open channel_mutex_inv(channel, channel->queue, inv, channel->counterId, emptinessCountingId)();
    //@ ghost_counter_destroy_ticket(channel->counterId);
    void *message = dequeue(channel->queue);
    //@ op();
    //@ open n_times(_, _);
    //@ open emptiness_ticket(channel, emptinessCountingId)();
    //@ close channel_mutex_inv(channel, channel->queue, inv, channel->counterId, emptinessCountingId)();
    mutex_release(channel->mutex);
    return message;
    //@ leak is_channel_receive_ghost_op(op, inv, P, Q);
    //@ assert counting_ticket(countingId, ?frac);
    //@ close [frac]channel_(channel)();
    //@ destroy_counting_ticket(countingId);
    //@ assert counting_ticket(emptinessCountingId, ?frac2);
    //@ close [frac2]channel_emptinessToken_(channel)();
    //@ destroy_counting_ticket(emptinessCountingId);
    //@ close channel_handle(channel, f, space, termScope, fs, level, creditObject, inv, sendTokens - 1);
}

void channel_dispose(channel channel)
    //@ requires channel_handle(channel, 1, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, 0);
    //@ ensures [fs]obligation_space(space, termScope) &*& inv(nil) &*& obspace_credit_object(creditObject, space, level, 0, 0);
    //@ terminates;
{
    //@ open channel_handle(channel, 1, space, termScope, fs, level, creditObject, inv, 0);
    //@ assert [1/2]channel(channel, _, _, _, _, _, _, _, _, ?countingId, ?emptinessCountingId);
    //@ destroy_counting_handle(countingId);
    //@ open channel_(channel)();
    //@ destroy_counting_handle(emptinessCountingId);
    //@ open channel_emptinessToken_(channel)();
    mutex_dispose(channel->mutex);
    //@ open channel_mutex_inv(channel, channel->queue, inv, channel->counterId, emptinessCountingId)();
    //@ open n_times(?n, _);
    //@ if (n != 0) { open emptiness_ticket(channel, emptinessCountingId)(); assert false; }
    sema_dispose(channel->sema);
    queue_dispose(channel->queue);
    free(channel);
    //@ assert inv(?elems);
    //@ switch (elems) { case nil: case cons(h, t): }
    //@ leak ghost_counter(_, _);
}
