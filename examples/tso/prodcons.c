#include <stdlib.h>
#include "tso.h"

struct buffer {
    void *contents;
    int cycle1;
    //@ int cycle;
    //@ int prodCycle;
    int prodCycle1;
    //@ int tso_id;
    void *lastWritten;
    //@ void *lastWritten1;
};

struct buffer buffer;

/*@

inductive state = state(int, void *);

predicate_ctor prodcons(predicate(void *) p)(state state) =
    state == state(?cycle, ?contents) &*&
    buffer_contents(&buffer, contents) &*&
    [1/2]buffer_cycle(&buffer, cycle) &*&
    [1/2]buffer_lastWritten1(&buffer, ?lastWritten) &*&
    [1/2]buffer_prodCycle(&buffer, ?prodCycle) &*&
    contents == 0 ?
        lastWritten == 0 ? cycle == prodCycle : cycle == prodCycle + 1
    :
        p(contents) &*& prodCycle == cycle &*& contents == lastWritten;

fixpoint bool state_le(state s1, state s2) {
    switch (s1) {
        case state(cycle1, contents1): return
            switch (s2) {
                case state(cycle2, contents2): return
                    cycle1 < cycle2 || cycle1 == cycle2 && (contents1 == 0 || contents2 == contents1);
            };
    }
}

predicate producer(predicate(void *) p) =
    [1/2]buffer_tso_id(&buffer, ?id) &*&
    [1/2]buffer_prodCycle(&buffer, ?prodCycle) &*&
    [1/2]buffer_lastWritten1(&buffer, ?lastWritten) &*&
    buffer_prodCycle1(&buffer, prodCycle) &*&
    buffer_lastWritten(&buffer, lastWritten) &*&
    [1/2]tso(id, prodcons(p), state_le, cons(prod_read_f, cons(prod_write_f, cons(cons_read_f, cons(cons_write_f, nil)))), state(prodCycle, lastWritten));

predicate consumer(predicate(void *) p) =
    [1/2]buffer_tso_id(&buffer, ?id) &*&
    buffer_cycle1(&buffer, ?cycle) &*&
    [1/2]buffer_cycle(&buffer, cycle) &*&
    [1/2]tso(id, prodcons(p), state_le, cons(prod_read_f, cons(prod_write_f, cons(cons_read_f, cons(cons_write_f, nil)))), state(cycle, 0));

fixpoint void *vararg_ptr_(vararg v) {
    switch (v) {
        case vararg_pointer(x): return x;
        default: return (void *)0;
    }
}

fixpoint int vararg_int_(vararg v) {
    switch (v) {
        case vararg_int(size, x): return x;
        default: return 0;
    }
}

fixpoint state prod_read_f0(void *contents0, int prodCycle, void *lastWritten) {
    return
        contents0 == 0 ?
            lastWritten == 0 ? state(prodCycle, 0) : state(prodCycle + 1, 0)
        :
            state(prodCycle, lastWritten);
}

fixpoint state prod_read_f(list<vararg> args, state dummy) {
    return prod_read_f0(vararg_ptr_(nth(0, args)), vararg_int_(nth(1, args)), vararg_ptr_(nth(2, args)));
}

fixpoint state prod_write_f0(void *element, int prodCycle, void *lastWritten) {
    return lastWritten == 0 ? state(prodCycle, element) : state(prodCycle + 1, element);
}

fixpoint state prod_write_f(list<vararg> args, state dummy) {
    return prod_write_f0(vararg_ptr_(nth(0, args)), vararg_int_(nth(1, args)), vararg_ptr_(nth(2, args)));
}

fixpoint state cons_read_f(list<vararg> args, state dummy) { return state(vararg_int_(nth(1, args)), vararg_ptr_(nth(0, args))); }

fixpoint state cons_write_f(list<vararg> args, state dummy) { return state(vararg_int_(nth(0, args)) + 1, 0); }

@*/

void init()
    /*@
    requires
        buffer_contents(&buffer, 0) &*&
        buffer_tso_id(&buffer, _) &*&
        buffer_cycle(&buffer, _) &*&
        buffer_cycle1(&buffer, 0) &*&
        buffer_prodCycle(&buffer, _) &*&
        buffer_lastWritten(&buffer, 0) &*&
        buffer_lastWritten1(&buffer, _) &*&
        buffer_prodCycle1(&buffer, 0) &*&
        exists<predicate(void *)>(?p);
    @*/
    //@ ensures producer(p) &*& consumer(p);
{
    //@ buffer.cycle = 0;
    //@ buffer.prodCycle = 0;
    //@ buffer.lastWritten1 = 0;
    {
        /*@
        lemma void state_le_refl(state s)
            requires true;
            ensures state_le(s, s) == true;
        {
            assert s == state(?cycle, ?contents);
        }
        lemma void state_le_trans(state s1, state s2, state s3)
            requires state_le(s1, s2) && state_le(s2, s3);
            ensures state_le(s1, s3) == true;
        {
            assert s1 == state(?cycle1, ?contents1);
            assert s2 == state(?cycle2, ?contents2);
            assert s3 == state(?cycle3, ?contents3);
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(state_le_refl) : le_refl<state>(state_le)(s) { call(); };
        //@ produce_lemma_function_pointer_chunk(state_le_trans) : le_trans<state>(state_le)(s1, s2, s3) { call(); };
        //@ close prodcons(p)(state(0, 0));
        //@ int id = create_tso(prodcons(p), state_le, {prod_read_f, prod_write_f, cons_read_f, cons_write_f}, state(0, 0));
        //@ buffer.tso_id = id;
    }
    //@ close producer(p);
    //@ close consumer(p);
}

void produce(void *element)
    //@ requires producer(?p) &*& element != 0 &*& p(element);
    //@ ensures producer(p);
{
    for (;;)
        //@ invariant producer(p) &*& p(element);
    {
        //@ open producer(p);
        void *lastWritten = buffer.lastWritten;
        int prodCycle = buffer.prodCycle1;
        prophecy_id contents0Id = create_tso_prophecy();
        //@ assert tso_prophecy(contents0Id, ?contents0);
        void *contents;
        {
            /*@
            predicate P() = true;
            lemma void ctxt(state s)
                requires state_le(state(prodCycle, lastWritten), s) == true &*& prodcons(p)(s) &*& is_tso_read_op(?op, &(&buffer)->contents, contents0, ?pre, ?post) &*& pre() &*& [_]P();
                ensures prodcons(p)(s) &*& state_le(prod_read_f0(contents0, prodCycle, lastWritten), s) == true &*& post() &*& is_tso_read_op(op, &(&buffer)->contents, contents0, pre, post);
            {
                open prodcons(p)(s);
                op();
                close prodcons(p)(s);
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(ctxt) : tso_read_ctxt<state>(&(&buffer)->contents, contents0, prodcons(p), state_le, state(prodCycle, lastWritten), prod_read_f0(contents0, prodCycle, lastWritten), P)(s) { call(); };
            //@ close P();
            //@ leak P();
            contents = tso_read(contents0Id, &(&buffer)->contents, 0, prodCycle, lastWritten);
        }
        if (contents == 0) {
            {
                /*@
                predicate P() = [1/2]buffer_prodCycle(&buffer, prodCycle) &*& [1/2]buffer_lastWritten1(&buffer, lastWritten) &*& p(element);
                predicate Q() = [1/2]buffer_prodCycle(&buffer, lastWritten == 0 ? prodCycle : prodCycle + 1) &*& [1/2]buffer_lastWritten1(&buffer, element);
                lemma void ctxt(state s1, state s2)
                    requires P() &*& state_le(prod_read_f0(contents0, prodCycle, lastWritten), s1) == true &*& state_le(s1, s2) == true &*& prodcons(p)(s2) &*& is_tso_write_op(?op, &(&buffer)->contents, element, ?pre, ?post) &*& pre();
                    ensures Q() &*& prodcons(p)(prod_write_f0(element, prodCycle, lastWritten)) &*& state_le(s2, prod_write_f0(element, prodCycle, lastWritten)) == true &*& state_le(prod_write_f0(element, prodCycle, lastWritten), prod_write_f0(element, prodCycle, lastWritten)) == true &*& post() &*& is_tso_write_op(op, &(&buffer)->contents, element, pre, post);
                {
                    open P();
                    open prodcons(p)(s2);
                    assert s1 == state(_, _);
                    void *oldContents = buffer.contents;
                    int cycle = buffer.cycle;
                    assume(0 <= cycle);
                    if (lastWritten != 0) {
                        assert cycle > prodCycle;
                        assert oldContents == 0;
                        buffer.prodCycle++;
                    }
                    buffer.lastWritten1 = element;
                    op();
                    close prodcons(p)(prod_write_f0(element, prodCycle, lastWritten));
                    close Q();
                }
                @*/
                //@ produce_lemma_function_pointer_chunk(ctxt) : tso_write_ctxt<state>(&(&buffer)->contents, element, prodcons(p), state_le, prod_read_f0(contents0, prodCycle, lastWritten), (prod_write_f)(cons(vararg_pointer(element), cons(vararg_int(sizeof(int), prodCycle), cons(vararg_pointer(lastWritten), nil)))), P, Q)(s1, s2) { call(); };
                //@ close P();
                tso_write(&(&buffer)->contents, element, 1, element, prodCycle, lastWritten);
                //@ open Q();
            }
            if (lastWritten != 0) { buffer.prodCycle1++; }
            buffer.lastWritten = element;
            //@ close producer(p);
            break;
        } else {
            //@ close producer(p);
        }
    }
}

void *consumer()
    //@ requires consumer(?p);
    //@ ensures consumer(p) &*& p(result);
{
    for (;;)
        //@ invariant consumer(p);
    {
        //@ open consumer(p);
        prophecy_id contents0Id = create_tso_prophecy();
        //@ assert tso_prophecy(contents0Id, ?contents0);
        int cycle = buffer.cycle1;
        void *contents;
        {
            /*@
            predicate P() = true;
            lemma void ctxt(state s)
                requires state_le(state(cycle, 0), s) == true &*& prodcons(p)(s) &*& is_tso_read_op(?op, &(&buffer)->contents, contents0, ?pre, ?post) &*& pre() &*& [_]P();
                ensures prodcons(p)(s) &*& state_le(state(cycle, contents0), s) == true &*& post() &*& is_tso_read_op(op, &(&buffer)->contents, contents0, pre, post);
            {
                open P();
                open prodcons(p)(s);
                assert s == state(?cycle1, ?contents1);
                op();
                close prodcons(p)(s);
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(ctxt) : tso_read_ctxt<state>(&(&buffer)->contents, contents0, prodcons(p), state_le, state(cycle, 0), state(cycle, contents0), P)(s) { call(); };
            //@ close P();
            //@ leak P();
            contents = tso_read(contents0Id, &(&buffer)->contents, 2, cycle);
        }
        if (contents != 0) {
            {
                /*@
                predicate P() = [1/2]buffer_cycle(&buffer, cycle);
                predicate Q() = [1/2]buffer_cycle(&buffer, cycle + 1) &*& p(contents);
                lemma void ctxt(state s1, state s2)
                    requires P() &*& state_le(state(cycle, contents), s1) == true &*& state_le(s1, s2) == true &*& prodcons(p)(s2) &*& is_tso_write_op(?op, &(&buffer)->contents, 0, ?pre, ?post) &*& pre();
                    ensures Q() &*& prodcons(p)(state(cycle + 1, 0)) &*& state_le(s2, state(cycle + 1, 0)) == true &*& state_le(state(cycle + 1, 0), state(cycle + 1, 0)) == true &*& post() &*& is_tso_write_op(op, &(&buffer)->contents, 0, pre, post);
                {
                    open P();
                    open prodcons(p)(s2);
                    assert s1 == state(?cycle1, ?contents1);
                    assert s2 == state(?cycle2, ?contents2);
                    assume(0 <= cycle2);
                    assert contents2 == contents;
                    op();
                    buffer.cycle++;
                    close prodcons(p)(state(cycle + 1, 0));
                    close Q();
                }
                @*/
                //@ produce_lemma_function_pointer_chunk(ctxt) : tso_write_ctxt<state>(&(&buffer)->contents, 0, prodcons(p), state_le, state(cycle, contents), (cons_write_f)(cons(vararg_int(sizeof(int), cycle), nil)), P, Q)(s1, s2) { call(); };
                //@ close P();
                tso_write(&(&buffer)->contents, 0, 3, cycle);
                //@ open Q();
            }
            buffer.cycle1++;
            //@ close consumer(p);
            return contents;
        } else {
            //@ close consumer(p);
        }
    }
}

//@ predicate integer0(void *p) = int_(p, _) &*& malloc_block_ints(p, 1);

int main() //@ : main_full(prodcons)
    //@ requires module(prodcons, true);
    //@ ensures true;
{
    //@ open_module();
    //@ close exists(integer0);
    init();
    for (;;)
      //@ invariant producer(integer0) &*& consumer(integer0);
    {
      int *x = malloc(1 * sizeof(int));
      if (x == 0) abort();
      //@ close integer0(x);
      produce(x);
      int *y = consumer();
      //@ open integer0(y);
      free(y);
    }
}