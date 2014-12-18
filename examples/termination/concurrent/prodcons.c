//@ #include "nat.gh"
#include "threading_with_obspaces.h"
#include "channels.h"
#include <stdlib.h>
//@ #include "../call_perms.gh"

struct info {
    channel channel;
    //@ int space;
    //@ int termScope;
    //@ level level;
    //@ int creditObject;
    //@ int nextToSend;
    //@ int nextToReceive;
};
typedef struct info *info;

/*@

predicate info(info info; channel channel, int space, int termScope, level level, int creditObject) =
    info->channel |-> channel &*&
    info->space |-> space &*&
    info->termScope |-> termScope &*&
    info->level |-> level &*&
    info->creditObject |-> creditObject;
 
fixpoint bool is_range(unsigned int a, list<void *> xs, unsigned int b) {
    switch (xs) {
        case nil: return a == b;
        case cons(x, xs0): return x == (void *)a && is_range(a + 1, xs0, b);
    }
}

lemma void is_range_append(unsigned int a, list<void *> xs, unsigned int b, list<void *> ys, unsigned int c)
    requires is_range(a, xs, b) && is_range(b, ys, c);
    ensures is_range(a, append(xs, ys), c) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            is_range_append(a + 1, xs0, b, ys, c);
    }
}

lemma void is_range_length(unsigned int a, list<void *> xs, unsigned int b)
    requires is_range(a, xs, b) == true;
    ensures length(xs) == b - a;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            is_range_length(a + 1, xs0, b);
    }
}

predicate_ctor channel_inv(info info)(list<void *> elems) =
    [1/2]info->nextToSend |-> ?nextToSend &*&
    [1/2]info->nextToReceive |-> ?nextToReceive &*&
    nextToReceive <= nextToSend &*&
    is_range(nextToReceive, elems, nextToSend) == true &*&
    nextToSend == 10 ?
        [1/2]info(info, _, ?space, ?termScope, _, _) &*& [1/2]info->nextToSend |-> _ &*& [1/3]obligation_space(space, termScope)
    :
        true;

predicate channel_send_tokens(int n, channel channel, int space, int termScope, level level, int creditObject, predicate(list<void *>) inv) =
    n == 0 ?
        emp
    :
        channel_send_token(channel, space, termScope, level, creditObject, inv) &*&
        channel_send_tokens(n - 1, channel, space, termScope, level, creditObject, inv);

fixpoint list<t> n_times<t>(nat n, t x) {
    switch (n) {
        case zero: return nil;
        case succ(n0): return cons(x, n_times(n0, x));
    }
}

lemma void level_all_above_or_eq_n_times(nat n, level level)
    requires true;
    ensures level_all_above_or_eq(n_times(n, level), level) == true;
{
    switch (n) {
        case zero:
        case succ(n0):
            level_all_above_or_eq_n_times(n0, level);
    }
}

fixpoint real real_of_nat(nat n) {
    switch (n) {
        case zero: return 0;
        case succ(n0): return real_of_nat(n0) + 1;
    }
}

fixpoint real real_of_int(int x) { return real_of_nat(nat_of_int(x)); }

lemma void real_of_int_plus(int x, int y)
    requires 0 <= x &*& 0 <= y;
    ensures real_of_int(x + y) == real_of_int(x) + real_of_int(y);
{
    int z = x;
    while (z != 0)
        invariant 0 <= z &*& real_of_int(z + y) - real_of_int(z) == real_of_int(x + y) - real_of_int(x);
        decreases z;
    {
        z--;
        succ_int(z);
        succ_int(z + y);
    }
}

predicate debits(int n, int creditObject) =
    n == 0 ? emp : debit(creditObject) &*& debits(n - 1, creditObject);

predicate_ctor producer_pre(int space_, int termScope_, level level_)(void *data) =
    [1/2]info(data, ?channel_, space_, termScope_, level_, ?creditObject_) &*& [1/2]info_nextToSend(data, 0) &*& debits(10, creditObject_) &*&
    channel_send_tokens(10, channel_, space_, termScope_, level_, creditObject_, channel_inv(data)) &*&
    [1/3]obligation_space(space_, termScope_) &*&
    [_]obspace_credit_object_info(creditObject_, space_, level_);

@*/

void producer(void *data)
    /*@
    requires
        [1/2]info(data, ?channel_, ?space_, ?termScope, ?level_, ?creditObject_) &*& [1/2]info_nextToSend(data, 0) &*& debits(10, creditObject_) &*&
        channel_send_tokens(10, channel_, space_, termScope, level_, creditObject_, channel_inv(data)) &*&
        [_]obspace_credit_object_info(creditObject_, space_, level_) &*& obspace_joinee(space_) &*&
        [1/3]obligation_space(space_, termScope) &*& obspace_obligation_set(space_, n_times(nat_of_int(10), level_));
    @*/
    //@ ensures stop_perm(termScope);
    //@ terminates;
{
    info info = data;
    channel channel = info->channel;
    //@ int space = info->space;
    //@ level level = info->level;
    //@ int creditObject = info->creditObject;
    for (unsigned int i = 0; i < 10; i = i + 1)
        /*@
        invariant
            i <= 10 &*&
            debits(10 - i, creditObject_) &*&
            channel_send_tokens(10 - i, channel, space, termScope, level, creditObject, channel_inv(info)) &*&
            [_]obspace_credit_object_info(creditObject_, space_, level_) &*&
            i < 10 ?
                obspace_obligation_set(space, n_times(nat_of_int(10 - i), level)) &*&
                [1/2]info(info, _, space, termScope, _, _) &*&
                [1/3]obligation_space(space, termScope) &*&
                [1/2]info->nextToSend |-> i &*&
                obspace_joinee(space_)
            :
                stop_perm(termScope);
        @*/
        //@ decreases 10 - (int)i;
    {
        //@ open channel_send_tokens(10 - i, channel, space, termScope, level, creditObject, channel_inv(info));
        //@ level_all_above_or_eq_n_times(nat_of_int(10 - i), level);
        {
            /*@
            predicate P() = [1/2]info->nextToSend |-> i &*& i == 9 ? [1/2]info(info, _, space, termScope, _, _) &*& [1/3]obligation_space(space, termScope) : true;
            predicate Q() = i < 9 ? [1/2]info->nextToSend |-> i + 1 : true;
            lemma void op()
                requires channel_inv(info)(?elems) &*& P();
                ensures channel_inv(info)(append(elems, {(void *)i})) &*& Q();
            {
                open channel_inv(info)(elems);
                open P();
                is_range_append(info->nextToReceive, elems, info->nextToSend, {(void *)i}, info->nextToSend + 1);
                info->nextToSend++;
                close Q();
                close channel_inv(info)(append(elems, {(void *)i}));
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(op) : channel_send_ghost_op(channel_inv(info), (void *)i, P, Q)() { call(); };
            //@ close P();
            //@ close exists(i == 9);
            //@ succ_int(0);
            //@ if (i == 9) { open debits(_, _); }
            channel_send(channel, (void *)i);
            //@ open Q();
        }
        //@ succ_int(i);
        //@ succ_int(10 - i - 1);
        /*@
        if (i < 9) {
            open debits(_, _);
            obspace_debit_dispose();
        }
        @*/
    }
    //@ open channel_send_tokens(0, _, _, _, _, _, _);
    //@ open debits(0, _);
}

/*@

lemma int create_obligation_space()
    requires term_perm(?termScope, false);
    ensures obligation_space(result, termScope) &*& obspace_obligation_set(result, nil);
{
    int scope = create_obligation_scope(stop_perm_(termScope));
    close obligation_space_inv(scope, termScope)();
    create_atomic_space(0, obligation_space_inv(scope, termScope));
    int space = create_ghost_cell(pair(scope, 0r));
    leak ghost_cell(space, _);
    close obligation_space(space, termScope);
    close obspace_obligation_set(space, nil);
    return space;
}

lemma void remove_all_append<t>(list<t> xs, list<t> ys)
    requires true;
    ensures remove_all(xs, append(xs, ys)) == ys;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            remove_remove_all(x0, xs0, append(xs, ys));
            remove_all_append(xs0, ys);
    }
}

predicate credits(int n, int creditObject) =
   n == 0 ? emp : credit(creditObject) &*& credits(n - 1, creditObject);

@*/

void main_term_scope(void *data)
    //@ requires term_perm(?termScope, false);
    //@ ensures term_perm(termScope, false);
    //@ terminates;
{
    //@ int space = create_obligation_space();
    //@ level level = create_level(nil, nil);
    //@ int creditObject = create_obspace_credit_object(space, level);
    //@ obspace_credit_object_get_info();
    info info = malloc(sizeof(struct info));
    if (info == 0) abort();
    //@ info->nextToSend = 0;
    //@ info->nextToReceive = 0;
    //@ info->space = space;
    //@ info->termScope = termScope;
    //@ info->level = level;
    //@ info->creditObject = creditObject;
    //@ close channel_inv(info)(nil);
    //@ close exists(channel_inv(info));
    //@ close exists<real>(1/3);
    channel channel = create_channel();
    info->channel = channel;
    //@ close debits(0, creditObject);
    //@ close credits(0, creditObject);
    /*@
    for (int i = 0; i < 10; i++)
        invariant
            0 <= i &*& i <= 10 &*&
            [_]obspace_credit_object_info(creditObject, space, level) &*& [2/3]obligation_space(space, termScope) &*&
            obspace_obligation_set(space, n_times(nat_of_int(i), level)) &*& debits(i, creditObject) &*& credits(i, creditObject);
        decreases 10 - i;
    {
        create_obspace_debit();
        close debits(i + 1, creditObject);
        close credits(i + 1, creditObject);
        succ_int(i);
    }
    @*/
    //@ close channel_send_tokens(0, channel, space, termScope, level, creditObject, channel_inv(info));
    /*@
    for (int i = 0; i < 10; i++)
        invariant
            0 <= i &*& i <= 10 &*&
            [2/3]obligation_space(space, termScope) &*&
            channel_handle(channel, 1, space, termScope, 1/3, level, creditObject, channel_inv(info), i) &*&
            channel_send_tokens(i, channel, space, termScope, level, creditObject, channel_inv(info));
        decreases 10 - i;
    {
        channel_create_send_token(channel);
        close channel_send_tokens(i + 1, channel, space, termScope, level, creditObject, channel_inv(info));
    }
    @*/
    /*@
    produce_function_pointer_chunk thread_run_with_obligations(producer)(termScope, space, n_times(nat_of_int(10), level), producer_pre(space, termScope, level))(data_) {
        open producer_pre(space, termScope, level)(data_);
        call();
    }
    @*/
    //@ remove_all_append(n_times(nat_of_int(10), level), nil);
    //@ assert remove_all(n_times(nat_of_int(10), level), n_times(nat_of_int(10), level)) == nil;
    //@ close [1/2]info(info, channel, space, termScope, level, creditObject);
    //@ close producer_pre(space, termScope, level)(info);
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main_term_scope);
    //@ consume_call_perm_for(producer);
    thread_start_with_obligations(producer, info);
    for (unsigned int i = 0; i < 10; i = i + 1)
        /*@
        invariant
            channel_handle(channel, 1, space, termScope, 1/3, level, creditObject, channel_inv(info), 10 - i) &*&
            [1/3]obligation_space(space, termScope) &*& obspace_obligation_set(space, nil) &*&
            credits(10 - i, creditObject) &*&
            [1/2]info->nextToReceive |-> i &*&
            0 <= i &*& i <= 10;
        @*/
        //@ decreases 10 - (int)i;
    {
        {
            /*@
            predicate P() =
                [1/2]info->nextToReceive |-> i;
            predicate Q(void *result) =
                [1/2]info->nextToReceive |-> i + 1 &*& result == (void *)i;
            lemma void op()
                requires channel_inv(info)(cons(?elem, ?elems)) &*& P();
                ensures channel_inv(info)(elems) &*& Q(elem);
            {
                open channel_inv(info)(_);
                open P();
                is_range_length(info->nextToReceive, cons(elem, elems), info->nextToSend);
                info->nextToReceive++;
                close channel_inv(info)(elems);
                close Q(elem);
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(op) : channel_receive_ghost_op(channel_inv(info), P, Q)() { call(); };
            //@ close P();
            //@ open credits(_, _);
            void *x = channel_receive(channel);
            //@ open Q(x);
            assert(x == (void *)i);
        }
    }
    channel_dispose(channel);
    //@ close [1/2]info(info, _, _, _, _, _);
    //@ open channel_inv(info)(nil);
    free(info);
    //@ open credits(0, creditObject);
    //@ leak obspace_credit_object(creditObject, space, level, 0, 0);
    //@ leak obspace_obligation_set(space, nil);
    //@ open obligation_space(space, termScope);
    //@ assert [_]ghost_cell<pair<int, real> >(space, pair(?scope, ?olevel));
    //@ leak atomic_space(olevel, obligation_space_inv(scope, termScope));
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    {
        /*@
        predicate true_(void *data;) = true;
        @*/
        //@ produce_function_pointer_chunk term_scope(main_term_scope)(true_, true_)(data) { call(); }
        //@ close true_(0);
        //@ produce_call_below_perm_();
        //@ call_below_perm__elim(main);
        //@ consume_call_perm_for(main_term_scope);
        call_term_scope(main_term_scope, 0);
        //@ open true_(0);
    }
    return 0;
}
