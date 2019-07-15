#include "stdlib.h"
#include "queue.h"
#include "threading.h"
//@ #include "ghost_cells.gh"

struct message {
    int id;
};

struct message *create_message(int id)
    //@ requires true;
    //@ ensures message_id(result, id) &*& malloc_block_message(result);
{
    struct message *message = malloc(sizeof(struct message));
    if (message == 0) abort();
    message->id = id;
    return message;
}

/*@

predicate messages(list<void *> messages, list<int> ids) =
    switch (messages) {
        case nil: return ids == nil;
        case cons(m0, ms1): return
            switch (ids) {
                case nil: return false;
                case cons(id0, ids1):
                   return message_id(m0, id0) &*& malloc_block_message(m0) &*& messages(ms1, ids1);
            };
    };

lemma void messages_append_lemma(list<void *> ms1)
    requires messages(ms1, ?ids1) &*& messages(?ms2, ?ids2);
    ensures messages(append(ms1, ms2), append(ids1, ids2));
{
    open messages(ms1, ids1);
    switch (ms1) {
        case nil:
        case cons(h, t):
            messages_append_lemma(t);
            close messages(append(ms1, ms2), append(ids1, ids2));
    }
}

fixpoint bool ids_ok(int minId, int maxId, list<int> ids) {
    switch (ids) {
        case nil: return true;
        case cons(h, t): return minId <= h && h <= maxId && ids_ok(h + 1, maxId, t);
    }
}

lemma void ids_ok_weaken(int minId1, int minId0, list<int> ids, int maxId0, int maxId1)
    requires minId1 <= minId0 &*& ids_ok(minId0, maxId0, ids) == true &*& maxId0 <= maxId1;
    ensures ids_ok(minId1, maxId1, ids) == true;
{
    switch (ids) {
        case nil:
        case cons(h, t):
            ids_ok_weaken(h + 1, h + 1, t, maxId0, maxId1);
    }
}

lemma void ids_ok_append_lemma(int minId1, int maxId1, list<int> ids1, int minId2, int maxId2, list<int> ids2)
    requires ids_ok(minId1, maxId1, ids1) == true &*& ids_ok(minId2, maxId2, ids2) == true &*& maxId1 < minId2 &*& minId1 <= minId2 &*& maxId1 <= maxId2;
    ensures ids_ok(minId1, maxId2, append(ids1, ids2)) == true;
{
    switch (ids1) {
        case nil:
            ids_ok_weaken(minId1, minId2, ids2, maxId2, maxId2);
        case cons(h, t):
            ids_ok_append_lemma(h + 1, maxId1, t, minId2, maxId2, ids2);
    }
}

predicate_ctor message_queue(struct queue *queue, int minIdCell, int maxIdCell)() =
    queue_state(queue, ?values) &*& messages(values, ?ids) &*&
    [1/2]ghost_cell<int>(minIdCell, ?minId) &*& [1/2]ghost_cell<int>(maxIdCell, ?maxId) &*&
    ids_ok(minId, maxId, ids) == true &*& minId <= maxId + 1;

predicate cell_ids(int minIdCell, int maxIdCell) = true;

predicate_family_instance thread_run_pre(consumer)(struct queue *queue, any info) =
    queue_consumer(queue) &*& cell_ids(?minIdCell, ?maxIdCell) &*& [1/2]ghost_cell<int>(minIdCell, 0) &*& [1/2]atomic_space(message_queue(queue, minIdCell, maxIdCell));

@*/

void consumer(struct queue *queue) //@ : thread_run
    //@ requires thread_run_pre(consumer)(queue, ?info);
    //@ ensures thread_run_post(consumer)(queue, info);
{
    //@ open thread_run_pre(consumer)(queue, _);
    //@ open cell_ids(?minIdCell, ?maxIdCell);
    
    int lastId = -1;
    while (true)
        //@ invariant queue_consumer(queue) &*& [1/2]ghost_cell<int>(minIdCell, ?minId) &*& lastId < minId &*& [1/2]atomic_space(message_queue(queue, minIdCell, maxIdCell));
    {
        bool success;
        struct message *message;
        {
            /*@
            predicate pre() = [1/2]ghost_cell<int>(minIdCell, minId);
            predicate post(bool result, void *value) =
                result ?
                    message_id(value, ?id) &*& malloc_block_message(value) &*& [1/2]ghost_cell<int>(minIdCell, id + 1) &*& minId <= id
                :
                    [1/2]ghost_cell<int>(minIdCell, minId);
            @*/
            /*@
            produce_lemma_function_pointer_chunk queue_try_dequeue_context(message_queue(queue, minIdCell, maxIdCell), queue, pre, post)() {
                open pre();
                open message_queue(queue, minIdCell, maxIdCell)();
                assert is_queue_try_dequeue_operation(?op, queue, ?P, ?Q);
                op();
                assert Q(?result, ?value);
                if (result) {
                    open messages(_, _);
                    struct message *m = value;
                    ghost_cell_mutate(minIdCell, m->id + 1);
                }
                close message_queue(queue, minIdCell, maxIdCell)();
                close post(result, value);
            };
            @*/
            //@ close pre();
            success = queue_try_dequeue(queue, &message);
            //@ leak is_queue_try_dequeue_context(_, _, _, _, _);
            //@ open post(_, _);
        }
        if (success) {
            int id = message->id;
            assert(lastId < id);
            lastId = id;
            free(message);
        }
    }
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct queue *queue = create_queue();
    //@ close messages(nil, nil);
    //@ int minIdCell = create_ghost_cell(0);
    //@ int maxIdCell = create_ghost_cell(-1);
    //@ close message_queue(queue, minIdCell, maxIdCell)();
    //@ create_atomic_space(message_queue(queue, minIdCell, maxIdCell));
    
    //@ close cell_ids(minIdCell, maxIdCell);
    //@ close thread_run_pre(consumer)(queue, unit);
    thread_start(consumer, queue);
    //@ leak thread(_, _, _, _);
    int id = 0;
    while (true)
        //@ invariant [1/2]atomic_space(message_queue(queue, minIdCell, maxIdCell)) &*& [1/2]ghost_cell<int>(maxIdCell, id - 1);
    {
        struct message *message = create_message(id);
        {
            /*@
            predicate pre() = [1/2]ghost_cell<int>(maxIdCell, id - 1) &*& message_id(message, id) &*& malloc_block_message(message);
            predicate post() = [1/2]ghost_cell<int>(maxIdCell, id);
            @*/
            /*@
            produce_lemma_function_pointer_chunk queue_enqueue_context(message_queue(queue, minIdCell, maxIdCell), queue, message, pre, post)() {
                open message_queue(queue, minIdCell, maxIdCell)();
                assert is_queue_enqueue_operation(?op, queue, message, ?P, ?Q);
                op();
                assert Q(?result);
                if (result) {
                    open pre();
                    assert [1/2]ghost_cell<int>(minIdCell, ?minId) &*& messages(?ms1, ?ids1);
                    close messages(nil, nil);
                    close messages({message}, {id});
                    messages_append_lemma(ms1);
                    ids_ok_append_lemma(minId, id - 1, ids1, id, id, {id});
                    ghost_cell_mutate(maxIdCell, id);
                    close post();
                }
                close message_queue(queue, minIdCell, maxIdCell)();
            };
            @*/
            //@ close pre();
            queue_enqueue(queue, message);
            //@ leak is_queue_enqueue_context(_, _, _, _, _, _);
            //@ open post();
        }
        if (id == 2147483647) abort();
        id++;
    }
}
