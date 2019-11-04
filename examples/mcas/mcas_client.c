#include <stdint.h>
#include <stdlib.h>
#include <threading.h>
#include "mcas.h"
//@ #include "bitops_ex.gh"

struct interval {
    void *a;
    void *b;
    //@ int id;
};

/*@

inductive interval_info = interval_info(struct interval *);

fixpoint struct interval *get_interval(interval_info info) {
    switch (info) {
        case interval_info(interval): return interval;
    }
}

predicate_family_instance mcas_sep(interval_sep)(interval_info info, int id, predicate() inv, mcas_unsep *unsep) =
    inv == interval_ctor(id, get_interval(info)) &*& unsep == interval_unsep;
predicate_family_instance mcas_unsep(interval_unsep)(interval_info info, int id, predicate() inv, mcas_sep *sep, list<pair<void *, void *> > cs) =
    interval_values(?a, ?b) &*& a == b &*&
    true == (((uintptr_t)a & 2) == 0) &*&
    true == (((uintptr_t)a & 1) == 0) &*&
    switch (info) {
        case interval_info(interval): return
            &interval->a != &interval->b &*&
            cs == cons(pair(&interval->a, a), cons(pair(&interval->b, b), nil)) &*&
            inv == interval_ctor(id, interval);
    } &*&
    sep == interval_sep;

lemma void interval_sep() : mcas_sep
    requires mcas_sep(interval_sep)(?info, ?id, ?inv, ?unsep) &*& inv();
    ensures mcas_unsep(unsep)(info, id, inv, interval_sep, ?cs) &*& mcas(id, interval_sep, unsep, info, cs);
{
    open mcas_sep(interval_sep)(?info_, _, _, _);
    struct interval *interval = 0;
    switch (info_) { case interval_info(i): interval = i; }
    open interval_ctor(id, interval)();
    assert interval_values(?a, ?b);
    assert mcas(_, _, _, _, ?cs);
    close mcas_unsep(interval_unsep)(info_, id, inv, interval_sep, cs);
}

lemma void interval_unsep() : mcas_unsep
    requires mcas_unsep(interval_unsep)(?info, ?id, ?inv, ?sep, ?cs) &*& mcas(id, sep, interval_unsep, info, cs);
    ensures mcas_sep(sep)(info, id, inv, interval_unsep) &*& inv();
{
    open mcas_unsep(interval_unsep)(?info_, _, _, _, _);
    close mcas_sep(interval_sep)(info_, id, inv, interval_unsep);
    close interval_ctor(id, get_interval(info_))();
}

predicate interval_values(void *a, void *b) = true;

predicate_ctor interval_ctor(int id, struct interval *interval)() =
    interval_values(?a, ?b) &*& a == b &*&
    &interval->a != &interval->b &*&
    true == (((uintptr_t)a & 2) == 0) &*&
    true == (((uintptr_t)a & 1) == 0) &*&
    mcas(id, interval_sep, interval_unsep, interval_info(interval), cons(pair(&interval->a, a), cons(pair(&interval->b, b), nil)));

predicate_family_instance thread_run_data(shift_interval)(struct interval *interval) =
    [_]interval->id |-> ?id &*& [_]atomic_space(interval_ctor(id, interval)) &*& &interval->a != &interval->b;

@*/

void shift_interval(struct interval *interval) //@ : thread_run
    //@ requires thread_run_data(shift_interval)(interval);
    //@ ensures true;
{
    //@ open thread_run_data(shift_interval)(_);
    //@ assert [_]interval->id |-> ?id;
    
    while (true)
        //@ invariant [_]atomic_space(interval_ctor(id, interval));
    {
        void *a0 = 0;
        void *b0 = 0;
        {
            /*@
            predicate_family_instance mcas_cs_mem(csMem)(mcas_unsep *unsep, any mcasInfo, void *a) =
                unsep == interval_unsep &*& mcasInfo == interval_info(interval) &*& a == &interval->a;
            lemma void csMem() : mcas_cs_mem
                requires mcas_cs_mem(csMem)(?unsep, ?mcasInfo, ?a) &*& mcas_unsep(unsep)(mcasInfo, ?id_, ?inv, ?sep, ?cs);
                ensures mcas_cs_mem(csMem)(unsep, mcasInfo, a) &*& mcas_unsep(unsep)(mcasInfo, id_, inv, sep, cs) &*& mem_assoc(a, cs) == true;
            {
                open mcas_cs_mem(csMem)(_, _, _);
                open mcas_unsep(interval_unsep)(?mcasInfo_, _, _, _, _);
                close mcas_unsep(interval_unsep)(mcasInfo_, id_, inv, sep, cs);
                close mcas_cs_mem(csMem)(unsep, mcasInfo, a);
            }
            predicate_family_instance mcas_read_pre(rop)(mcas_unsep *unsep, any mcasInfo, void *a) =
                unsep == interval_unsep &*& mcasInfo == interval_info(interval) &*& a == &interval->a;
            predicate_family_instance mcas_read_post(rop)(void *result) =
                true == (((uintptr_t)result & 1) == 0) &*&
                true == (((uintptr_t)result & 2) == 0);
            lemma void rop() : mcas_read_op
                requires mcas_read_pre(rop)(?unsep, ?mcasInfo, ?a) &*& mcas_unsep(unsep)(mcasInfo, ?id_, ?inv, ?sep, ?cs);
                ensures mcas_read_post(rop)(assoc(a, cs)) &*& mcas_unsep(unsep)(mcasInfo, id_, inv, sep, cs);
            {
                open mcas_read_pre(rop)(_, _, _);
                open mcas_unsep(interval_unsep)(?mcasInfo_, _, ?inv_, _, _);
                close mcas_unsep(interval_unsep)(mcasInfo_, id_, inv_, interval_sep, cs);
                close mcas_read_post(rop)(assoc(a, cs));
            }
            @*/
            //@ close mcas_cs_mem(csMem)(interval_unsep, interval_info(interval), &interval->a);
            //@ close mcas_sep(interval_sep)(interval_info(interval), id, interval_ctor(id, interval), interval_unsep);
            //@ close mcas_read_pre(rop)(interval_unsep, interval_info(interval), &interval->a);
            //@ produce_lemma_function_pointer_chunk(interval_sep);
            //@ produce_lemma_function_pointer_chunk(interval_unsep);
            //@ produce_lemma_function_pointer_chunk(csMem);
            //@ produce_lemma_function_pointer_chunk(rop);
            a0 = mcas_read(&interval->a);
            //@ leak is_mcas_sep(interval_sep);
            //@ leak is_mcas_unsep(interval_unsep);
            //@ leak is_mcas_cs_mem(csMem);
            //@ leak is_mcas_read_op(rop);
            //@ open mcas_sep(interval_sep)(_, _, _, _);
            //@ open mcas_cs_mem(csMem)(_, _, _);
            //@ open mcas_read_post(rop)(_);
        }
        /*@
        invariant
            [_]atomic_space(interval_ctor(id, interval)) &*&
            true == (((uintptr_t)a0 & 1) == 0) &*&
            true == (((uintptr_t)a0 & 2) == 0);
        @*/
        { 
            /*@
            predicate_family_instance mcas_cs_mem(csMem)(mcas_unsep *unsep, any mcasInfo, void *a) =
                unsep == interval_unsep &*& mcasInfo == interval_info(interval) &*& a == &interval->b;
            lemma void csMem() : mcas_cs_mem
                requires mcas_cs_mem(csMem)(?unsep, ?mcasInfo, ?a) &*& mcas_unsep(unsep)(mcasInfo, ?id_, ?inv, ?sep, ?cs);
                ensures mcas_cs_mem(csMem)(unsep, mcasInfo, a) &*& mcas_unsep(unsep)(mcasInfo, id_, inv, sep, cs) &*& mem_assoc(a, cs) == true;
            {
                open mcas_cs_mem(csMem)(_, _, _);
                open mcas_unsep(interval_unsep)(?mcasInfo_, _, _, _, _);
                close mcas_unsep(interval_unsep)(mcasInfo_, id_, inv, sep, cs);
                close mcas_cs_mem(csMem)(unsep, mcasInfo, a);
            }
            predicate_family_instance mcas_read_pre(rop)(mcas_unsep *unsep, any mcasInfo, void *a) =
                unsep == interval_unsep &*& mcasInfo == interval_info(interval) &*& a == &interval->b;
            predicate_family_instance mcas_read_post(rop)(void *result) =
                true == (((uintptr_t)result & 1) == 0) &*&
                true == (((uintptr_t)result & 2) == 0);
            lemma void rop() : mcas_read_op
                requires mcas_read_pre(rop)(?unsep, ?mcasInfo, ?a) &*& mcas_unsep(unsep)(mcasInfo, ?id_, ?inv, ?sep, ?cs);
                ensures mcas_read_post(rop)(assoc(a, cs)) &*& mcas_unsep(unsep)(mcasInfo, id_, inv, sep, cs);
            {
                open mcas_read_pre(rop)(_, _, _);
                open mcas_unsep(interval_unsep)(?mcasInfo_, _, ?inv_, _, _);
                close mcas_unsep(interval_unsep)(mcasInfo_, id_, inv_, interval_sep, cs);
                close mcas_read_post(rop)(assoc(a, cs));
            }
            @*/
            //@ close mcas_cs_mem(csMem)(interval_unsep, interval_info(interval), &interval->b);
            //@ close mcas_sep(interval_sep)(interval_info(interval), id, interval_ctor(id, interval), interval_unsep);
            //@ close mcas_read_pre(rop)(interval_unsep, interval_info(interval), &interval->b);
            //@ produce_lemma_function_pointer_chunk(interval_unsep);
            //@ produce_lemma_function_pointer_chunk(interval_sep);
            //@ produce_lemma_function_pointer_chunk(csMem);
            //@ produce_lemma_function_pointer_chunk(rop);
            b0 = mcas_read(&interval->b);
            //@ leak is_mcas_sep(interval_sep);
            //@ leak is_mcas_unsep(interval_unsep);
            //@ leak is_mcas_cs_mem(csMem);
            //@ leak is_mcas_read_op(rop);
            //@ open mcas_sep(interval_sep)(_, _, _, _);
            //@ open mcas_cs_mem(csMem)(_, _, _);
            //@ open mcas_read_post(rop)(_);
        }
        
        if (SIZE_MAX / 2 < sizeof(struct mcas_entry)) abort();
        struct mcas_entry *entries = malloc(2 * sizeof(struct mcas_entry));
        if (entries == 0) abort();
        //@ leak malloc_block(entries, _); // We assume the presence of a garbage collector.
        //@ chars_split((char *)(void *)entries, sizeof(struct mcas_entry));
        //@ close_struct(entries + 0);
        (entries + 0)->a = &interval->a;
        (entries + 0)->o = a0;
        if (UINTPTR_MAX - 4 < (uintptr_t)a0) abort();
        (entries + 0)->n = a0 + 4;
        //@ bitand_plus_4(a0);
        //@ close_struct(entries + 1);
        (entries + 1)->a = &interval->b;
        (entries + 1)->o = b0;
        if (UINTPTR_MAX - 4 < (uintptr_t)b0) abort();
        (entries + 1)->n = b0 + 4;
        //@ bitand_plus_4(b0);
        //@ close entries(0, entries + 2, nil);
        //@ close entries(1, entries + 1, cons(pair(&interval->b, pair(b0, b0 + 4)), nil));
        //@ close entries(2, entries, cons(pair(&interval->a, pair(a0, a0 + 4)), cons(pair(&interval->b, pair(b0, b0 + 4)), nil)));
        //@ assert entries(_, _, ?es);
        bool success = false;
        {
            /*@
            predicate_family_instance mcas_mem(mem)(mcas_unsep *unsep, any mcasInfo, list<pair<void *, pair<void *, void *> > > es_) =
                unsep == interval_unsep &*& mcasInfo == interval_info(interval) &*&
                es_ == cons(pair(&interval->a, pair(a0, a0 + 4)), cons(pair(&interval->b, pair(b0, b0 + 4)), nil));
            lemma void mem() : mcas_mem
                requires mcas_mem(mem)(?unsep, ?mcasInfo, ?es_) &*& mcas_unsep(unsep)(mcasInfo, ?id_, ?inv, ?sep, ?cs);
                ensures mcas_mem(mem)(unsep, mcasInfo, es_) &*& mcas_unsep(unsep)(mcasInfo, id_, inv, sep, cs) &*& mem_es(es_, cs) == true;
            {
                open mcas_mem(mem)(_, _, _);
                open mcas_unsep(interval_unsep)(?mcasInfo_, _, _, _, _);
                close mcas_unsep(interval_unsep)(mcasInfo_, id_, inv, sep, cs);
                close mcas_mem(mem)(unsep, mcasInfo, es);
            }
            predicate_family_instance mcas_pre(op)(mcas_unsep *unsep, any mcasInfo, list<pair<void *, pair<void *, void *> > > es_) =
                unsep == interval_unsep &*& mcasInfo == interval_info(interval) &*& es_ == es;
            predicate_family_instance mcas_post(op)(bool result) =
                result ? a0 == b0 : true;
            lemma bool op() : mcas_op
                requires mcas_pre(op)(?unsep, ?mcasInfo, ?es_) &*& mcas_unsep(unsep)(mcasInfo, ?id_, ?inv, ?sep, ?cs);
                ensures
                    mcas_post(op)(result) &*&
                    result == es_success(es_, cs) &*&
                    mcas_unsep(unsep)(mcasInfo, id_, inv, sep, ?cs1) &*&
                    result ? cs1 == es_apply(es_, cs) : cs1 == cs;
            {
                open mcas_pre(op)(_, _, _);
                open mcas_unsep(interval_unsep)(?mcasInfo_, _, _, _, _);
                open interval_values(?a, ?b);
                if (a == a0 && b == b0) {
                    close interval_values(a + 4, b + 4);
                    assert cs == cons(pair(&interval->a, a), cons(pair(&interval->b, b), nil));
                    assert es == cons(pair(&interval->a, pair(a, a + 4)), cons(pair(&interval->b, pair(b, b + 4)), nil));
                    assert es_apply(cons(pair(&interval->a, pair(a, a + 4)), nil), cons(pair(&interval->a, a), nil)) == cons(pair(&interval->a, a + 4), nil);
                    assert
                        es_apply(
                            cons(pair(&interval->a, pair(a, a + 4)), nil),
                            cons(pair(&interval->a, a), cons(pair(&interval->b, b), nil)))
                        == cons(pair(&interval->a, a + 4), cons(pair(&interval->b, b), nil));
                    assert
                        update_assoc(
                            cons(pair(&interval->a, a), cons(pair(&interval->b, b), nil)),
                            &interval->b,
                            b + 4)
                        == cons(pair(&interval->a, a), cons(pair(&interval->b, b + 4), nil));
                    assert
                        es_apply(
                            cons(pair(&interval->b, pair(b, b + 4)), nil),
                            cons(pair(&interval->a, a), cons(pair(&interval->b, b), nil)))
                        == cons(pair(&interval->a, a), cons(pair(&interval->b, b + 4), nil));
                    assert es_apply(es, cs) == cons(pair(&interval->a, a + 4), cons(pair(&interval->b, b + 4), nil));
                    close mcas_unsep(interval_unsep)(mcasInfo_, id_, inv, sep, es_apply(es, cs));
                    close mcas_post(op)(true);
                    return true;
                } else {
                    close interval_values(a, b);
                    close mcas_unsep(interval_unsep)(mcasInfo_, id_, inv, sep, cs);
                    close mcas_post(op)(false);
                    return false;
                }
            }
            @*/
            //@ close mcas_mem(mem)(interval_unsep, interval_info(interval), es);
            //@ close mcas_pre(op)(interval_unsep, interval_info(interval), es);
            //@ close mcas_sep(interval_sep)(interval_info(interval), id, interval_ctor(id, interval), interval_unsep);
            //@ produce_lemma_function_pointer_chunk(mem);
            //@ produce_lemma_function_pointer_chunk(op);
            //@ produce_lemma_function_pointer_chunk(interval_sep);
            //@ produce_lemma_function_pointer_chunk(interval_unsep);
            //@ assert &interval->a != &interval->b;
            success = mcas(2, entries);
            //@ leak is_mcas_unsep(interval_unsep);
            //@ leak is_mcas_sep(interval_sep);
            //@ leak is_mcas_op(op);
            //@ leak is_mcas_mem(mem);
            //@ open mcas_sep(interval_sep)(_, _, _, _);
            //@ open mcas_post(op)(_);
            //@ open mcas_mem(mem)(_, _, _);
        }
        if (success)
            assert(a0 == b0);
    }
}

/*@

lemma void interval_fields_disjoint(struct interval *i)
    requires i->a |-> ?a &*& i->b |-> ?b;
    ensures i->a |-> a &*& i->b |-> b &*& &i->a != &i->b;
{
    pointer_distinct(&i->a, &i->b);
}

@*/

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct interval *interval = malloc(sizeof(struct interval));
    if (interval == 0) abort();
    //@ leak malloc_block_interval(interval); // We assume the presence of a garbage collector.
    interval->a = 0;
    interval->b = 0;
    //@ int id = create_mcas(interval_sep, interval_unsep, interval_info(interval));
    //@ interval->id = id;
    //@ interval_fields_disjoint(interval);
    //@ bitand_def(0, Zsign(false), 1, Zdigit(Zsign(false), true));
    //@ assert ((0 & 1) == 0);
    //@ bitand_def(0, Zsign(false), 2, Zdigit(Zdigit(Zsign(false), true), false));
    //@ assert ((0 & 2) == 0);
    //@ close interval_values(0, 0);
    //@ open interval_a(_, _);
    //@ open interval_b(_, _);
    //@ mcas_add_cell(id, &interval->b);
    //@ mcas_add_cell(id, &interval->a);
    //@ close interval_ctor(id, interval)();
    //@ create_atomic_space(interval_ctor(id, interval));
    //@ leak atomic_space(_);
    //@ leak interval->id |-> id;
    //@ close thread_run_data(shift_interval)(interval);
    thread_start(shift_interval, interval);
    //@ close thread_run_data(shift_interval)(interval);
    shift_interval(interval);
    return 0;
}