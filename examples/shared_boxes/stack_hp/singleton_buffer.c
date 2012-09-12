#include "stdlib.h"
#include "malloc.h" 
#include "atomics.h"
#include "threading.h"

/*
   A buffer with only one space
   
   Simple example to explain the use of atomics 
*/
struct singleton_buffer {
    void *data;
};

/*@
predicate_ctor singleton_buffer_inv(struct singleton_buffer* buf)() = 
    buf->data |-> ?data &*& 
    (data == 0 ? true : integer(data, _) &*& malloc_block(data, sizeof(int)));

predicate singleton_buffer(struct singleton_buffer* buf) = 
    malloc_block_singleton_buffer(buf) &*&
    atomic_space(singleton_buffer_inv(buf));

@*/

bool sb_try_enqueue(struct singleton_buffer* buf, void* data)
//@ requires [?f]singleton_buffer(buf) &*& integer(data, _) &*& malloc_block(data, sizeof(int)) &*& data != 0;
//@ ensures [f]singleton_buffer(buf) &*& (result ? true : integer(data, _) &*& malloc_block(data, sizeof(int)));
{
    //@ open [f]singleton_buffer(buf);
    void* casresult;
    //@ void *resultProphecy = create_prophecy_pointer();
    {
        /*@ 
        predicate_family_instance atomic_compare_and_store_pointer_context_pre(ctxt)(predicate() inv_, void **pp, void *old, void *new, void *prophecy) =
            inv_ == singleton_buffer_inv(buf) &*& 
            pp == &buf->data &*& 
            old == 0 &*& 
            new == data &*& 
            prophecy == resultProphecy &*&
            integer(data, _) &*& malloc_block(data, sizeof(int));
        predicate_family_instance atomic_compare_and_store_pointer_context_post(ctxt)() =
            resultProphecy == 0 ? true : integer(data, _) &*& malloc_block(data, sizeof(int));
        lemma void ctxt(atomic_compare_and_store_pointer_operation *op) : atomic_compare_and_store_pointer_context
            requires
                atomic_compare_and_store_pointer_context_pre(ctxt)(?inv_, ?pp, ?old, ?new, ?prophecy) &*& 
                inv_() &*&
                is_atomic_compare_and_store_pointer_operation(op) &*&
                atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy);
            ensures
                atomic_compare_and_store_pointer_context_post(ctxt)() &*& 
                inv_() &*&
                is_atomic_compare_and_store_pointer_operation(op) &*&
                atomic_compare_and_store_pointer_operation_post(op)();
        {
            open atomic_compare_and_store_pointer_context_pre(ctxt)(_, _, _, _, _);
            open singleton_buffer_inv(buf)();
            op();
            close singleton_buffer_inv(buf)();
            close atomic_compare_and_store_pointer_context_post(ctxt)();
        }
    @*/
        //@ close atomic_compare_and_store_pointer_context_pre(ctxt)(singleton_buffer_inv(buf), &buf->data, 0, data, resultProphecy);
        //@ produce_lemma_function_pointer_chunk(ctxt);
        casresult = atomic_compare_and_store_pointer(&buf->data, 0, data);
        //@ open atomic_compare_and_store_pointer_context_post(ctxt)();
        //@ leak is_atomic_compare_and_store_pointer_context(ctxt);
    }
    //@ close [f]singleton_buffer(buf);
    return casresult == 0;
}

bool sb_try_dequeue(struct singleton_buffer* buf, void** res)
//@ requires [?f]singleton_buffer(buf) &*& pointer(res, ?data);
//@ ensures [f]singleton_buffer(buf) &*& (result ? pointer(res, ?newdata) &*& integer(newdata, _)  &*& malloc_block(newdata, sizeof(int)): pointer(res, data));
{
    //@ open [f]singleton_buffer(buf);
    void* tmp; 
    //@ void *dataProphecy = create_prophecy_pointer();
    {
        /*@
        predicate_family_instance atomic_load_pointer_context_pre(ctxt)(predicate() inv_, void **pp, void *prophecy) =
            inv_ == singleton_buffer_inv(buf) &*& 
            pp == &buf->data &*& 
            prophecy == dataProphecy;
        predicate_family_instance atomic_load_pointer_context_post(ctxt)() =
            true;
        lemma void ctxt(atomic_load_pointer_operation *op) : atomic_load_pointer_context
            requires 
                atomic_load_pointer_context_pre(ctxt)(?inv_, ?pp, ?prophecy) &*& inv_() &*&
                is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
            ensures
                atomic_load_pointer_context_post(ctxt)() &*& inv_() &*&
                is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();
        {
            open atomic_load_pointer_context_pre(ctxt)(inv_, pp, prophecy);
            open singleton_buffer_inv(buf)();
            op();
            close singleton_buffer_inv(buf)();
            close atomic_load_pointer_context_post(ctxt)();
        }
        @*/
        //@ close atomic_load_pointer_context_pre(ctxt)(singleton_buffer_inv(buf), &buf->data, dataProphecy);
        //@ produce_lemma_function_pointer_chunk(ctxt);
        tmp = atomic_load_pointer(&buf->data);
        //@ open atomic_load_pointer_context_post(ctxt)();
        //@ leak is_atomic_load_pointer_context(ctxt);
    }
    if(tmp == 0) {
        //@ close [f]singleton_buffer(buf);
        return false;
    }
    //@ void *resultProphecy = create_prophecy_pointer();
    void* casresult; 
    {
        /*@ 
        predicate_family_instance atomic_compare_and_store_pointer_context_pre(ctxt)(predicate() inv_, void **pp, void *old, void *new, void *prophecy) =
            inv_ == singleton_buffer_inv(buf) &*& 
            pp == &buf->data &*& 
            old == tmp &*& 
            new == 0 &*& 
            prophecy == resultProphecy;
        predicate_family_instance atomic_compare_and_store_pointer_context_post(ctxt)() =
            resultProphecy == tmp ? integer(tmp, _) &*& malloc_block(tmp, sizeof(int)) : true;
        lemma void ctxt(atomic_compare_and_store_pointer_operation *op) : atomic_compare_and_store_pointer_context
            requires
                atomic_compare_and_store_pointer_context_pre(ctxt)(?inv_, ?pp, ?old, ?new, ?prophecy) &*& 
                inv_() &*&
                is_atomic_compare_and_store_pointer_operation(op) &*&
                atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy);
            ensures
                atomic_compare_and_store_pointer_context_post(ctxt)() &*& 
                inv_() &*&
                is_atomic_compare_and_store_pointer_operation(op) &*&
                atomic_compare_and_store_pointer_operation_post(op)();
        {
            open atomic_compare_and_store_pointer_context_pre(ctxt)(_, _, _, _, _);
            open singleton_buffer_inv(buf)();
            op();
            close singleton_buffer_inv(buf)();
            close atomic_compare_and_store_pointer_context_post(ctxt)();
        }
    @*/
        //@ close atomic_compare_and_store_pointer_context_pre(ctxt)(singleton_buffer_inv(buf), &buf->data, tmp, 0, resultProphecy);
        //@ produce_lemma_function_pointer_chunk(ctxt);
        casresult = atomic_compare_and_store_pointer(&buf->data, tmp, 0);
        //@ open atomic_compare_and_store_pointer_context_post(ctxt)();
        //@ leak is_atomic_compare_and_store_pointer_context(ctxt);
    }
    //@ close [f]singleton_buffer(buf);
    if(casresult == tmp) {
        *res = tmp;
        return true;
    }
    return false;
}

struct singleton_buffer* sb_create() 
//@ requires true;
//@ ensures result == 0 ? true : singleton_buffer(result);
{
    struct singleton_buffer* result = malloc(sizeof(struct singleton_buffer));
    if(result != 0) {
        result->data = 0;
        //@ close singleton_buffer_inv(result)();
        //@ create_atomic_space(singleton_buffer_inv(result));
        //@ close singleton_buffer(result);
    }
    return result;
}

void sb_dispose(struct singleton_buffer* buf) 
//@ requires singleton_buffer(buf);
//@ ensures true;
{
    //@ open singleton_buffer(buf);
    //@ dispose_atomic_space(singleton_buffer_inv(buf));
    //@ open singleton_buffer_inv(buf)();
    void* data = buf->data;
    if(data != 0) {
        //@integer_to_chars(data);
        free(data);
    }
    free(buf);
}

/*@

predicate_family_instance thread_run_data(consumer)(void *buf) = [?f]singleton_buffer(buf);

predicate_family_instance thread_run_data(producer)(void *buf) = [?f]singleton_buffer(buf);

@*/

void consumer(struct singleton_buffer *buf) //@ : thread_run
    //@ requires thread_run_data(consumer)(buf) &*& lockset(currentThread, nil);
    //@ ensures lockset(currentThread, nil);
{
    //@ open thread_run_data(consumer)(buf);
    void* data;
    while(true) 
    //@ invariant [?f]singleton_buffer(buf) &*& pointer(&data, _);
    {
        bool result = sb_try_dequeue(buf, &data);
        if(result) {
            int* tmp = (int*) data;
            free(tmp); 
        }
    }
}

void producer(struct singleton_buffer *buf) //@ : thread_run
    //@ requires thread_run_data(producer)(buf) &*& lockset(currentThread, nil);
    //@ ensures lockset(currentThread, nil);
{
    //@ open thread_run_data(producer)(buf);
    while(true) 
    //@ invariant [?f]singleton_buffer(buf);
    {
        int* data = malloc(sizeof(int));
        while(data != 0) 
        //@ invariant [f]singleton_buffer(buf) &*& data == 0 ? true : integer(data, _) &*& malloc_block(data, sizeof(int));
        {
            bool result = sb_try_enqueue(buf, data);
            if(result) {
                data = 0;
            }
        }
    }
}

int main(int argc, char **argv) //@ : main
    //@ requires 0 <= argc &*& [_]char_array(argv, argc);
    //@ ensures true;
{
    struct singleton_buffer* buf = sb_create();
    if(buf == 0) return -1;
    //@ open [1/2] singleton_buffer(buf);
    //@ close thread_run_data(consumer)(buf);
    thread_start(consumer, buf);    
    //@ close [1/2] singleton_buffer(buf);
    //@ close thread_run_data(producer)(buf);
    thread_start(producer, buf);
    
    // busy waiting forever
    while(true)
    //@ invariant true;
    { 
    }
    return 0;
}
