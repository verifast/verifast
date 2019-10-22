#include <stdlib.h>
#include "atomics.h"

#include "splitcounter.h"
//@ #include "ghost_lists.gh"

struct counter {
    int left;
    int right;
    //@ int ghostListId;
};

/*@

inductive reader_info = reader_info(predicate() pre, predicate(int) post, int left, int right0, int right);

predicate_ctor reader(predicate(int) inv, int left, int right)(reader_info reader) =
    reader == reader_info(?pre, ?post, ?readerLeft, ?readerRight0, ?readerRight) &*&
    readerLeft <= left &*&
    readerRight0 <= right &*&
    readerRight < readerRight0 || left + right < readerLeft + readerRight ?
        is_read_ghop(_, inv, pre, post) &*&
        pre()
    :
        post(readerLeft + readerRight);

predicate_ctor counter_inv(struct counter *counter, predicate(int) inv)() =
    counter->left |-> ?left &*&
    counter->right |-> ?right &*&
    inv(left + right) &*&
    [1/2]counter->ghostListId |-> ?ghostListId &*&
    ghost_list(ghostListId, ?readers) &*&
    foreach(readers, reader(inv, left, right));

predicate counter(struct counter *counter, predicate(int) inv) =
    atomic_space(counter_inv(counter, inv)) &*&
    [1/2]counter->ghostListId |-> _ &*&
    malloc_block_counter(counter);

@*/

struct counter *create_counter()
    //@ requires exists<predicate(int)>(?inv) &*& inv(0);
    //@ ensures counter(result, inv);
{
    //@ open exists(_);
    struct counter *counter = malloc(sizeof(struct counter));
    if (counter == 0) abort();
    counter->left = 0;
    counter->right = 0;
    //@ int ghostListId = create_ghost_list<reader_info>();
    //@ counter->ghostListId = ghostListId;
    //@ close foreach(nil, reader(inv, 0, 0));
    //@ close counter_inv(counter, inv)();
    //@ create_atomic_space(counter_inv(counter, inv));
    //@ close counter(counter, inv);
    return counter;
}

void dispose_counter(struct counter *c)
    //@ requires counter(c, ?inv);
    //@ ensures inv(_);
{
    //@ open counter(c, inv);
    //@ dispose_atomic_space();
    //@ open counter_inv(c, inv)();
    free(c);
    //@ leak ghost_list(_, ?readers) &*& foreach(readers, _);
}

void incr_left(struct counter *counter)
    //@ requires [?f]counter(counter, ?inv) &*& is_incr_ghop(?ghop, inv, ?pre, ?post) &*& pre();
    //@ ensures [f]counter(counter, inv) &*& is_incr_ghop(ghop, inv, pre, post) &*& post();
{
    //@ open counter(counter, inv);
    {
        /*@
        predicate pre_() = is_incr_ghop(ghop, inv, pre, post) &*& pre();
        predicate post_() = is_incr_ghop(ghop, inv, pre, post) &*& post();
        lemma void ghop_()
            requires counter_inv(counter, inv)() &*& is_atomic_increment_int_op(?op, &counter->left, ?P, ?Q) &*& P() &*& pre_();
            ensures counter_inv(counter, inv)() &*& is_atomic_increment_int_op(op, &counter->left, P, Q) &*& Q() &*& post_();
        {
            open counter_inv(counter, inv)();
            open pre_();
            int left = counter->left;
            int right = counter->right;
            op();
            ghop();
            {
                lemma void iter()
                    requires foreach(?readers, reader(inv, left, right)) &*& inv(left + right + 1);
                    ensures foreach(readers, reader(inv, left + 1, right)) &*& inv(left + right + 1);
                {
                    open foreach(readers, reader(inv, left, right));
                    if (readers != nil) {
                        assert head(readers) == reader_info(?readerPre, ?readerPost, ?readerLeft, ?readerRight0, ?readerRight);
                        open reader(inv, left, right)(head(readers));
                        if (readerLeft + readerRight == left + right + 1) {
                            assert is_read_ghop(?readerGhop, _, _, _);
                            readerGhop();
                            leak is_read_ghop(_, _ ,_, _);
                        }
                        close reader(inv, left + 1, right)(head(readers));
                        iter();
                    }
                    close foreach(readers, reader(inv, left + 1, right));
                }
                iter();
            }
            close post_();
            close counter_inv(counter, inv)();
        }
        @*/
        //@ close pre_();
        //@ produce_lemma_function_pointer_chunk(ghop_) : atomic_increment_int_ghop(counter_inv(counter, inv), &counter->left, pre_, post_)() { call(); };
        atomic_increment_int(&counter->left);
        //@ leak is_atomic_increment_int_ghop(_, _, _, _, _);
        //@ open post_();
    }
    //@ close [f]counter(counter, inv);
}

void incr_right(struct counter *counter)
    //@ requires [?f]counter(counter, ?inv) &*& is_incr_ghop(?ghop, inv, ?pre, ?post) &*& pre();
    //@ ensures [f]counter(counter, inv) &*& is_incr_ghop(ghop, inv, pre, post) &*& post();
{
    //@ open counter(counter, inv);
    {
        /*@
        predicate pre_() = is_incr_ghop(ghop, inv, pre, post) &*& pre();
        predicate post_() = is_incr_ghop(ghop, inv, pre, post) &*& post();
        lemma void ghop_()
            requires counter_inv(counter, inv)() &*& is_atomic_increment_int_op(?op, &counter->right, ?P, ?Q) &*& P() &*& pre_();
            ensures counter_inv(counter, inv)() &*& is_atomic_increment_int_op(op, &counter->right, P, Q) &*& Q() &*& post_();
        {
            open counter_inv(counter, inv)();
            open pre_();
            int left = counter->left;
            int right = counter->right;
            op();
            ghop();
            {
                lemma void iter()
                    requires foreach(?readers, reader(inv, left, right)) &*& inv(left + right + 1);
                    ensures foreach(readers, reader(inv, left, right + 1)) &*& inv(left + right + 1);
                {
                    open foreach(readers, reader(inv, left, right));
                    if (readers != nil) {
                        assert head(readers) == reader_info(?readerPre, ?readerPost, ?readerLeft, ?readerRight0, ?readerRight);
                        open reader(inv, left, right)(head(readers));
                        if (readerLeft + readerRight == left + right + 1) {
                            assert is_read_ghop(?readerGhop, _, _, _);
                            readerGhop();
                            leak is_read_ghop(_, _ ,_, _);
                        }
                        close reader(inv, left, right + 1)(head(readers));
                        iter();
                    }
                    close foreach(readers, reader(inv, left, right + 1));
                }
                iter();
            }
            close post_();
            close counter_inv(counter, inv)();
        }
        @*/
        //@ close pre_();
        //@ produce_lemma_function_pointer_chunk(ghop_) : atomic_increment_int_ghop(counter_inv(counter, inv), &counter->right, pre_, post_)() { call(); };
        atomic_increment_int(&counter->right);
        //@ leak is_atomic_increment_int_ghop(_, _, _, _, _);
        //@ open post_();
    }
    //@ close [f]counter(counter, inv);
}

long long read(struct counter *counter)
    //@ requires [?f]counter(counter, ?inv) &*& is_read_ghop(?ghop, inv, ?pre, ?post) &*& pre();
    //@ ensures [f]counter(counter, inv) &*& post(result);
{
    //@ open counter(counter, inv);
    //@ int ghostListId = counter->ghostListId;
    prophecy_id leftId = create_prophecy();
    //@ assert prophecy(leftId, ?readerLeft);
    prophecy_id rightId = create_prophecy();
    //@ assert prophecy(rightId, ?readerRight);
    int l;
    {
        /*@
        predicate pre_() = [f/2]counter->ghostListId |-> ghostListId &*& is_read_ghop(ghop, inv, pre, post) &*& pre();
        predicate post_() = [f/2]counter->ghostListId |-> ghostListId &*& ghost_list_member_handle(ghostListId, reader_info(pre, post, readerLeft, _, readerRight));
        lemma void ghop_()
            requires counter_inv(counter, inv)() &*& is_atomic_load_int_op(?op, &counter->left, readerLeft, ?P, ?Q) &*& P() &*& pre_();
            ensures counter_inv(counter, inv)() &*& is_atomic_load_int_op(op, &counter->left, readerLeft, P, Q) &*& Q() &*& post_();
        {
            open counter_inv(counter, inv)();
            open pre_();
            op();
            close counter_left(counter, ?left);
            int right = counter->right;
            assert ghost_list(_, ?readers);
            ghost_list_insert(counter->ghostListId, nil, readers, reader_info(pre, post, readerLeft, right, readerRight));
            if (readerRight == right) {
                ghop();
                leak is_read_ghop(_, _, _, _);
            }
            close reader(inv, left, right)(reader_info(pre, post, readerLeft, right, readerRight));
            close foreach(cons(reader_info(pre, post, readerLeft, right, readerRight), readers), reader(inv, left, right));
            close post_();
            close counter_inv(counter, inv)();
        }
        @*/
        //@ close pre_();
        //@ produce_lemma_function_pointer_chunk(ghop_) : atomic_load_int_ghop(counter_inv(counter, inv), &counter->left, readerLeft, pre_, post_)() { call(); };
        l = atomic_load_int(leftId, &counter->left);
        //@ leak is_atomic_load_int_ghop(_, _, _, _, _, _);
        //@ open post_();
    }
    int r;
    {
        /*@
        predicate pre_() = [f/2]counter->ghostListId |-> ghostListId &*& ghost_list_member_handle(ghostListId, reader_info(pre, post, readerLeft, _, readerRight));
        predicate post_() = [f/2]counter->ghostListId |-> ghostListId &*& post(readerLeft + readerRight);
        lemma void ghop_()
            requires counter_inv(counter, inv)() &*& is_atomic_load_int_op(?op, &counter->right, readerRight, ?P, ?Q) &*& P() &*& pre_();
            ensures counter_inv(counter, inv)() &*& is_atomic_load_int_op(op, &counter->right, readerRight, P, Q) &*& Q() &*& post_();
        {
            open counter_inv(counter, inv)();
            open pre_();
            int left = counter->left;
            op();
            ghost_list_member_handle_lemma();
            assert ghost_list(_, ?readers);
            assert ghost_list_member_handle(_, reader_info(_, _, _, ?readerRight0, _));
            {
                lemma void iter(list<reader_info> readers0)
                    requires
                        foreach(?readers1, reader(inv, left, readerRight)) &*&
                        mem(reader_info(pre, post, readerLeft, readerRight0, readerRight), readers1) == true &*&
                        ghost_list_member_handle(ghostListId, reader_info(pre, post, readerLeft, readerRight0, readerRight)) &*&
                        ghost_list(ghostListId, readers) &*&
                        readers == append(readers0, readers1);
                    ensures
                        foreach(?readers2, reader(inv, left, readerRight)) &*&
                        ghost_list(ghostListId, ?newReaders) &*&
                        newReaders == append(readers0, readers2) &*&
                        post(readerLeft + readerRight);
                {
                    open foreach(_, _);
                    if (head(readers1) == reader_info(pre, post, readerLeft, readerRight0, readerRight)) {
                        ghost_list_remove(ghostListId, readers0, tail(readers1), reader_info(pre, post, readerLeft, readerRight0, readerRight));
                        open reader(inv, left, readerRight)(head(readers1));
                    } else {
                        append_assoc(readers0, {head(readers1)}, tail(readers1));
                        iter(append(readers0, {head(readers1)}));
                        assert foreach(?readers2, reader(inv, left, readerRight));
                        append_assoc(readers0, {head(readers1)}, readers2);
                        close foreach(cons(head(readers1), readers2), reader(inv, left, readerRight));
                    }
                }
                iter(nil);
            }
            close post_();
            close counter_inv(counter, inv)();
        }
        @*/
        //@ close pre_();
        //@ produce_lemma_function_pointer_chunk(ghop_) : atomic_load_int_ghop(counter_inv(counter, inv), &counter->right, readerRight, pre_, post_)() { call(); };
        r = atomic_load_int(rightId, &counter->right);
        //@ leak is_atomic_load_int_ghop(_, _, _, _, _, _);
        //@ open post_();
    }
    return (long long)l + r;
    //@ close [f]counter(counter, inv);
}
