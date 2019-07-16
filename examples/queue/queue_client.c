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

inductive consumer_context_info = consumer_context_info(struct queue *queue, int minIdCell, int maxIdCell, int minId);

predicate_family_instance queue_try_dequeue_context_pre(consumer_context)(consumer_context_info info, predicate() inv, struct queue *queue) =
    switch (info) {
        case consumer_context_info(queue_, minIdCell, maxIdCell, minId):
            return queue_ == queue &*& inv == message_queue(queue, minIdCell, maxIdCell) &*& [1/2]ghost_cell<int>(minIdCell, minId);
    };

predicate_family_instance queue_try_dequeue_context_post(consumer_context)(consumer_context_info info, bool result, void *value) =
    switch (info) {
        case consumer_context_info(queue, minIdCell, maxIdCell, minId):
            return
                result ?
                    message_id(value, ?id) &*& malloc_block_message(value) &*& minId <= id &*& [1/2]ghost_cell<int>(minIdCell, ?minId1) &*& id < minId1
                :
                    [1/2]ghost_cell<int>(minIdCell, minId);
    };

lemma bool consumer_context(queue_try_dequeue_operation *op) : queue_try_dequeue_context
    requires
        queue_try_dequeue_context_pre(consumer_context)(?info, ?inv, ?queue) &*& inv() &*& queue_try_dequeue_operation_pre(op)(?opInfo, queue) &*&
        is_queue_try_dequeue_operation(op);
    ensures
        queue_try_dequeue_context_post(consumer_context)(info, result, ?value) &*& inv() &*& queue_try_dequeue_operation_post(op)(opInfo, result, value) &*&
        is_queue_try_dequeue_operation(op);
{
    open queue_try_dequeue_context_pre(consumer_context)(?info_, inv, queue);
    switch (info_) {
        case consumer_context_info(queue_, minIdCell, maxIdCell, minId):
            open message_queue(queue, minIdCell, maxIdCell)();
            op();
            assert queue_try_dequeue_operation_post(op)(_, ?success, ?value) &*& queue_state(queue, ?newValues);
            if (success) {
                open messages(_, _);
                assert message_id(value, ?id);
                ghost_cell_mutate(minIdCell, id + 1);
            }
            close queue_try_dequeue_context_post(consumer_context)(info_, success, value);
            close message_queue(queue, minIdCell, maxIdCell)();
            return success;
    }
}

@*/

struct dequeue_result {
    struct message *message;
};

void consumer(struct queue *queue) //@ : thread_run
    //@ requires thread_run_pre(consumer)(queue, ?info);
    //@ ensures thread_run_post(consumer)(queue, info);
{
    //@ open thread_run_pre(consumer)(queue, _);
    //@ open cell_ids(?minIdCell, ?maxIdCell);
    struct dequeue_result *result = malloc(sizeof(struct dequeue_result));
    if (result == 0) abort();
    
    int lastId = -1;
    while (true)
        //@ invariant dequeue_result_message(result, _) &*& queue_consumer(queue) &*& [1/2]ghost_cell<int>(minIdCell, ?minId) &*& lastId < minId &*& [1/2]atomic_space(message_queue(queue, minIdCell, maxIdCell));
    {
        /*@
        close queue_try_dequeue_context_pre(consumer_context)(consumer_context_info(queue, minIdCell, maxIdCell, minId), message_queue(queue, minIdCell, maxIdCell), queue);
        @*/
        //@ open dequeue_result_message(result, _);
        //@ produce_lemma_function_pointer_chunk(consumer_context);
        bool success = queue_try_dequeue(queue, &result->message);
        //@ leak is_queue_try_dequeue_context(_);
        //@ assert pointer(&result->message, ?value);
        //@ close dequeue_result_message(result, value);
        //@ open queue_try_dequeue_context_post(consumer_context)(_, _, _);
        if (success) {
            int id = result->message->id;
            assert(lastId < id);
            lastId = id;
            free(result->message);
        }
    }
}

/*@

inductive main_context_info = main_context_info(struct queue *queue, int minIdCell, int maxIdCell, int id);

predicate_family_instance queue_enqueue_context_pre(main_context)(main_context_info info, predicate() inv, struct queue *queue, void *value) =
    switch (info) {
        case main_context_info(queue_, minIdCell, maxIdCell, id): return
            queue_ == queue &*&
            inv == message_queue(queue, minIdCell, maxIdCell) &*&
            message_id(value, id) &*& malloc_block_message(value) &*&
            [1/2]ghost_cell<int>(maxIdCell, id - 1);
    };

predicate_family_instance queue_enqueue_context_post(main_context)(main_context_info info) =
    switch (info) {
        case main_context_info(queue, minIdCell, maxIdCell, id):
            return [1/2]ghost_cell<int>(maxIdCell, id);
    };

lemma bool main_context(queue_enqueue_operation *op) : queue_enqueue_context
    requires
        queue_enqueue_context_pre(main_context)(?info, ?inv, ?queue, ?value) &*& inv() &*& queue_enqueue_operation_pre(op)(?opInfo, queue, value) &*&
        is_queue_enqueue_operation(op);
    ensures
        queue_enqueue_operation_post(op)(opInfo, result) &*& inv() &*&
        is_queue_enqueue_operation(op) &*&
        result ?
            queue_enqueue_context_post(main_context)(info)
        :
            queue_enqueue_context_pre(main_context)(info, inv, queue, value);
{
    open queue_enqueue_context_pre(main_context)(?info_, inv, queue, value);
    switch (info_) {
        case main_context_info(queue_, minIdCell, maxIdCell, id):
            open message_queue(queue, minIdCell, maxIdCell)();
            assert ghost_cell<int>(maxIdCell, ?maxId);
            bool success = op();
            if (success) {
                assert messages(?ms1, ?ids1);
                close messages(nil, nil);
                close messages(cons(value, nil), cons(id, nil));
                messages_append_lemma(ms1);
                assert [1/2]ghost_cell<int>(minIdCell, ?minId);
                ids_ok_append_lemma(minId, maxId, ids1, id, id, cons(id, nil));
                ghost_cell_mutate(maxIdCell, id);
                split_fraction ghost_cell(maxIdCell, _);
                close message_queue(queue, minIdCell, maxIdCell)();
                close queue_enqueue_context_post(main_context)(info_);
            } else {
                split_fraction ghost_cell(maxIdCell, _);
                close message_queue(queue, minIdCell, maxIdCell)();
                close queue_enqueue_context_pre(main_context)(info_, inv, queue, value);
            }
            return success;
    }
}

@*/

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
        /*@
        close
            queue_enqueue_context_pre(main_context)
                (main_context_info(queue, minIdCell, maxIdCell, id), message_queue(queue, minIdCell, maxIdCell), queue, message);
        @*/
        //@ produce_lemma_function_pointer_chunk(main_context);
        queue_enqueue(queue, message);
        //@ leak is_queue_enqueue_context(_);
        //@ open queue_enqueue_context_post(main_context)(_);
        if (id == 2147483647) abort();
        id++;
    }
}
