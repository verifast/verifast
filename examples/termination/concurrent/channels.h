#ifndef CHANNELS_H
#define CHANNELS_H

//@ #include <nat.gh>
//@ #include "obligation_spaces.gh"
//@ #include "credit_objects.gh"
//@ #include "obspace_credit_objects.gh"

/*

Deadlock-preventing specification approach based on [K.R.M. Leino, P. Mueller, J. Smans. Deadlock-free channels and locks. ESOP 2010].

This is not the most general possible specification. It is a tradeoff between generality and simplicity.
A more general specification would require a credit only at the point of blocking.
This spec does not support e.g. the case where you know that any one of two channels may block, but they will not both block.

*/

struct channel;
typedef struct channel *channel;

/*@

predicate channel_handle(channel channel, real frac, int space, int termScope, real spaceFrac, level level, int creditObject, predicate(list<void *>) inv, int sendTokens);
predicate channel_send_token(channel channel, int space, int termScope, level level, int creditObject, predicate(list<void *>) inv);

lemma void channel_create_send_token(channel channel);
    nonghost_callers_only
    requires channel_handle(channel, ?f, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, ?sendTokens);
    ensures channel_handle(channel, f, space, termScope, fs, level, creditObject, inv, sendTokens + 1) &*& channel_send_token(channel, space, termScope, level, creditObject, inv);

lemma void channel_handle_split(channel channel, real f1, int sendTokens1);
    nonghost_callers_only
    requires channel_handle(channel, ?f, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, ?sendTokens) &*& 0 < f1 &*& f1 < f;
    ensures channel_handle(channel, f1, space, termScope, fs, level, creditObject, inv, sendTokens1) &*& channel_handle(channel, f - f1, space, termScope, fs, level, creditObject, inv, sendTokens - sendTokens1);

lemma void channel_handle_merge(channel channel);
    nonghost_callers_only
    requires channel_handle(channel, ?f1, ?space1, ?termScope1, ?fs1, ?level1, ?creditObject1, ?inv1, ?sendTokens1) &*& channel_handle(channel, ?f2, ?space2, ?termScope2, ?fs2, ?level2, ?creditObject2, ?inv2, ?sendTokens2);
    ensures channel_handle(channel, f1 + f2, space1, termScope1, fs1, level1, creditObject1, inv1, sendTokens1 + sendTokens2) &*&
        space2 == space1 &*& termScope2 == termScope1 &*& fs2 == fs1 &*& level2 == level1 &*& creditObject2 == creditObject1 &*& inv2 == inv1;

@*/

channel create_channel();
    //@ requires exists<real>(?fs) &*& 0 < fs &*& [fs]obligation_space(?space, ?termScope) &*& obspace_credit_object(?creditObject, space, ?level, 0, 0) &*& exists<predicate(list<void *>)>(?inv) &*& inv(nil);
    //@ ensures channel_handle(result, 1, space, termScope, fs, level, creditObject, inv, 0);
    //@ terminates;

/*@

typedef lemma void channel_send_ghost_op(predicate(list<void *>) inv, void *message, predicate() P, predicate() Q)();
    requires inv(?elems) &*& P();
    ensures inv(append(elems, {message})) &*& Q();

@*/

void channel_send(channel channel, void *message);
    /*@
    requires
        channel_send_token(channel, ?space, ?termScope, ?level, ?creditObject, ?inv) &*&
        obspace_obligation_set(space, ?obs) &*& level_all_above_or_eq(obs, level) == true &*&
        is_channel_send_ghost_op(_, inv, message, ?P, ?Q) &*& P()
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

/*@

typedef lemma void channel_receive_ghost_op(predicate(list<void *>) inv, predicate() P, predicate(void *) Q)();
    requires inv(cons(?elem, ?elems)) &*& P();
    ensures inv(elems) &*& Q(elem);

@*/

void *channel_receive(channel channel);
    /*@
    requires
        channel_handle(channel, ?f, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, ?sendTokens) &*&
        obspace_obligation_set(space, ?obs) &*& level_all_above(obs, level) == true &*&
        credit(creditObject) &*&
        is_channel_receive_ghost_op(_, inv, ?P, ?Q) &*& P();
    @*/
    /*@
    ensures
        channel_handle(channel, f, space, termScope, fs, level, creditObject, inv, sendTokens - 1) &*&
        obspace_obligation_set(space, obs) &*&
        Q(result);
    @*/
    //@ terminates;

void channel_dispose(channel channel);
    //@ requires channel_handle(channel, 1, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, 0);
    //@ ensures [fs]obligation_space(space, termScope) &*& inv(nil) &*& obspace_credit_object(creditObject, space, level, 0, 0);
    //@ terminates;

#endif
