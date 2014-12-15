#ifndef SEMAS_H
#define SEMAS_H

#include "threading_terminates.h"
//@ #include "obligation_spaces.gh"
//@ #include "credit_objects.gh"
//@ #include "obspace_credit_objects.gh"

/*

Deadlock-preventing specification approach based on [K.R.M. Leino, P. Mueller, J. Smans. Deadlock-free channels and locks. ESOP 2010].

*/

struct sema;
typedef struct sema *sema;

/*@

predicate n_times(int n, predicate() p) =
    n == 0 ?
        emp
    :
        p() &*& n_times(n - 1, p);

lemma_auto void n_times_nonnegative();
    requires n_times(?n, ?p);
    ensures n_times(n, p) &*& 0 <= n;

predicate sema_handle(sema sema, real frac, int space, int termScope, real spaceFrac, level level, int creditObject, predicate() inv, int releaseTokens);
predicate sema_release_token(sema sema, int space, int termScope, level level, int creditObject, predicate() inv);

lemma void sema_create_release_token(sema sema);
    nonghost_callers_only
    requires sema_handle(sema, ?f, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, ?releaseTokens);
    ensures sema_handle(sema, f, space, termScope, fs, level, creditObject, inv, releaseTokens + 1) &*& sema_release_token(sema, space, termScope, level, creditObject, inv);

lemma void sema_handle_split(sema sema, real f1, int releaseTokens1);
    nonghost_callers_only
    requires sema_handle(sema, ?f, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, ?releaseTokens) &*& 0 < f1 &*& f1 < f;
    ensures sema_handle(sema, f1, space, termScope, fs, level, creditObject, inv, releaseTokens1) &*& sema_handle(sema, f - f1, space, termScope, fs, level, creditObject, inv, releaseTokens - releaseTokens1);

lemma void sema_handle_merge(sema sema);
    nonghost_callers_only
    requires sema_handle(sema, ?f1, ?space1, ?termScope1, ?fs1, ?level1, ?creditObject1, ?inv1, ?releaseTokens1) &*& sema_handle(sema, ?f2, ?space2, ?termScope2, ?fs2, ?level2, ?creditObject2, ?inv2, ?releaseTokens2);
    ensures sema_handle(sema, f1 + f2, space1, termScope1, fs1, level1, creditObject1, inv1, releaseTokens1 + releaseTokens2) &*&
        space2 == space1 &*& termScope2 == termScope1 &*& fs2 == fs1 &*& level2 == level1 &*& creditObject2 == creditObject1 &*& inv2 == inv1;

@*/

sema create_sema();
    //@ requires exists<real>(?fs) &*& [fs]obligation_space(?space, ?termScope) &*& obspace_credit_object(?creditObject, space, ?level, 0, 0) &*& exists<predicate()>(?inv);
    //@ ensures sema_handle(result, 1, space, termScope, fs, level, creditObject, inv, 0);
    //@ terminates;

void sema_acquire(sema sema);
    /*@
    requires
        sema_handle(sema, ?f, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, ?releaseTokens) &*&
        obspace_obligation_set(space, ?obs) &*& level_all_above(obs, level) == true &*&
        credit(creditObject);
    @*/
    /*@
    ensures
        sema_handle(sema, f, space, termScope, fs, level, creditObject, inv, releaseTokens - 1) &*&
        obspace_obligation_set(space, obs) &*&
        inv();
    @*/
    //@ terminates;

void sema_release(sema sema);
    /*@
    requires
        sema_release_token(sema, ?space, ?termScope, ?level, ?creditObject, ?inv) &*& inv() &*&
        exists<bool>(?final) &*&
        final ?
            obspace_obligation_set(space, {level}) &*& debit(creditObject) &*& obspace_joinee(space) &*&
            ensures stop_perm(termScope)
        :
            ensures credit(creditObject);
    @*/
    //@ ensures true;
    //@ terminates;

void sema_dispose(sema sema);
    //@ requires sema_handle(sema, 1, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, 0);
    //@ ensures [fs]obligation_space(space, termScope) &*& obspace_credit_object(creditObject, space, level, 0, 0);
    //@ terminates;

#endif
