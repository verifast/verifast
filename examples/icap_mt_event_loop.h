#ifndef ELOOP_H
#define ELOOP_H

struct eloop;

typedef struct eloop *eloop;

//@ predicate eloop(eloop x);

/*@

lemma void eloop_dup(eloop x);
    requires eloop(x);
    ensures eloop(x) &*& eloop(x);

@*/

typedef void eloop_handler/*@(eloop x, predicate(void *) dataPred)@*/(void *data);
    //@ requires eloop(x) &*& [_]dataPred(data);
    //@ ensures eloop(x) &*& [_]dataPred(data);

eloop eloop_create();
    //@ requires true;
    //@ ensures eloop(result);

void eloop_loop(eloop x);
    //@ requires eloop(x);
    //@ ensures eloop(x);

void eloop_signal(eloop x);
    //@ requires eloop(x);
    //@ ensures eloop(x);

void eloop_when(eloop x, eloop_handler *h, void *data);
    //@ requires eloop(x) &*& h == 0 ? true : [_]is_eloop_handler(h, x, ?dataPred) &*& [_]dataPred(data);
    //@ ensures eloop(x);

#endif