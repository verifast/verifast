#include "atomic_integer.h"
#include "threading.h"
#include "stdlib.h"

/* ghost */ struct state {
  //@ int vcopy;
  //@ bool reader_waiting;
  //@ bool writer_waiting;
};

/*@ predicate_ctor I(int* data, struct state* state)(int v) = 
 [1/2]state->vcopy |-> v &*& [1/2]state->reader_waiting |-> ?rw &*& [1/2]state->writer_waiting |-> ?ww &*&  
 (v == 0 ? 
   rw == true &*& (ww ? integer(data, _) &*& [1/2]state->vcopy |-> 0 &*& [1/4]state->writer_waiting |-> true &*& [1/4]state->reader_waiting |-> true :  true) 
 : 
   v == 1 &*& ww == true &*& (rw == true ? integer(data, _) &*& [1/2]state->vcopy |-> 1 &*& [1/4]state->reader_waiting |-> true &*& [1/4]state->writer_waiting |-> true : true)); 
@*/
void produce(int* x, int* data, /* ghost */ struct state* state)
  //@ requires [?f]atomic_integer(x, I(data, state)) &*& integer(data, _) &*& [1/4]state->reader_waiting |-> true &*& [1/2]state->writer_waiting |-> false &*& [1/2]state->vcopy |-> 0;
  //@ ensures [f]atomic_integer(x, I(data, state)) &*& integer(data, _) &*& [1/4]state->reader_waiting |-> true &*& [1/2]state->writer_waiting |-> false &*& [1/2]state->vcopy |-> 0;
{
  int sent = 7;
  *data = sent;
  {
    /*@
    predicate_family_instance atomic_integer_set_pre(my_atomic_integer_set_lemma)(int v) = integer(data, _) &*& [1/2]state->writer_waiting |-> false &*& [1/2]state->vcopy |-> 0 &*& [1/4]state->reader_waiting |-> true;
    predicate_family_instance atomic_integer_set_post(my_atomic_integer_set_lemma)(int old, int new) = [1/4]state->writer_waiting |-> true;
    lemma void my_atomic_integer_set_lemma()
      requires atomic_integer_set_pre(my_atomic_integer_set_lemma)(1) &*& I(data, state)(?old);
      ensures atomic_integer_set_post(my_atomic_integer_set_lemma)(old, 1) &*& I(data, state)(1);
    {
      open atomic_integer_set_pre(my_atomic_integer_set_lemma)(1);
      open I(data, state)(old);
      state->writer_waiting = true;
      state->vcopy = 1;
      close atomic_integer_set_post(my_atomic_integer_set_lemma)(old, 1);
      close I(data, state)(1);
    }
    @*/
    //@ produce_lemma_function_pointer_chunk(my_atomic_integer_set_lemma) : atomic_integer_set_lemma(1, I(data, state))() { call();};
    //@ close atomic_integer_set_pre(my_atomic_integer_set_lemma)(1);
    atomic_integer_set(x, 1);
    //@ open atomic_integer_set_post(my_atomic_integer_set_lemma)(_, 1);
  }
  while(true) 
    //@ invariant [f]atomic_integer(x, I(data, state)) &*& [1/4]state->writer_waiting |-> true;
  {
    /*@
    predicate_family_instance atomic_integer_get_pre(my_atomic_integer_get_lemma)() = [1/4]state->writer_waiting |-> true;
    predicate_family_instance atomic_integer_get_post(my_atomic_integer_get_lemma)(int value) = [1/4]state->writer_waiting |-> ?waiting &*& value != 0 ? waiting == true : integer(data, _) &*& [1/2]state->vcopy |-> 0 &*& [1/4]state->reader_waiting |-> true &*& [1/4]state->writer_waiting |-> false;
    lemma void my_atomic_integer_get_lemma()
      requires atomic_integer_get_pre(my_atomic_integer_get_lemma)() &*& I(data, state)(?value);
      ensures atomic_integer_get_post(my_atomic_integer_get_lemma)(value) &*& I(data, state)(value);
    {
      open atomic_integer_get_pre(my_atomic_integer_get_lemma)();
      open I(data, state)(value);
      if(value != 0) {
      } else {
        state->writer_waiting = false;
      }
      close I(data, state)(value);
      close atomic_integer_get_post(my_atomic_integer_get_lemma)(value);
      
    }
    @*/
    //@ produce_lemma_function_pointer_chunk(my_atomic_integer_get_lemma) : atomic_integer_get_lemma(I(data, state))() { call();};
    //@ close atomic_integer_get_pre(my_atomic_integer_get_lemma)();
    int cval = atomic_integer_get(x);
    //@ open atomic_integer_get_post(my_atomic_integer_get_lemma)(cval);
    if(cval == 0)
      break;
  }
}

void consume(int* x, int* data, struct state* state)
  //@ requires [?f]atomic_integer(x, I(data, state)) &*& [1/4]state->reader_waiting |-> true;
  //@ ensures [f]atomic_integer(x, I(data, state)) &*& [1/4]state->reader_waiting |-> true;
{
  while(true) 
    //@ invariant [f]atomic_integer(x, I(data, state)) &*& [1/4]state->reader_waiting |-> true;
  {
    /*@
    predicate_family_instance atomic_integer_get_pre(my_atomic_integer_get_lemma)() = [1/4]state->reader_waiting |-> true;
    predicate_family_instance atomic_integer_get_post(my_atomic_integer_get_lemma)(int value) = [1/4]state->reader_waiting |-> ?waiting &*& value == 0 ? waiting == true : integer(data, _) &*& [1/2]state->vcopy |-> 1 &*& [1/4]state->reader_waiting |-> false &*& [1/4]state->writer_waiting |-> true;
    lemma void my_atomic_integer_get_lemma()
      requires atomic_integer_get_pre(my_atomic_integer_get_lemma)() &*& I(data, state)(?value);
      ensures atomic_integer_get_post(my_atomic_integer_get_lemma)(value) &*& I(data, state)(value);
    {
      open atomic_integer_get_pre(my_atomic_integer_get_lemma)();
      open I(data, state)(value);
      if(value != 0) {
        state->reader_waiting = false;
      }
      close I(data, state)(value);
      close atomic_integer_get_post(my_atomic_integer_get_lemma)(value);
      
    }
    @*/
    //@ produce_lemma_function_pointer_chunk(my_atomic_integer_get_lemma) : atomic_integer_get_lemma(I(data, state))() { call();};
    //@ close atomic_integer_get_pre(my_atomic_integer_get_lemma)();
    int cval = atomic_integer_get(x);
    //@ open atomic_integer_get_post(my_atomic_integer_get_lemma)(cval);
    if(cval != 0)
      break;
  }
  int read = *data;
  {
    /*@
    predicate_family_instance atomic_integer_set_pre(my_atomic_integer_set_lemma)(int v) = integer(data, _) &*& [1/4]state->writer_waiting |-> true &*& [1/2]state->vcopy |-> 1 &*& [1/2]state->reader_waiting |-> false;
    predicate_family_instance atomic_integer_set_post(my_atomic_integer_set_lemma)(int old, int new) = [1/4]state->reader_waiting |-> true;
    lemma void my_atomic_integer_set_lemma()
     requires atomic_integer_set_pre(my_atomic_integer_set_lemma)(0) &*& I(data, state)(?old);
     ensures atomic_integer_set_post(my_atomic_integer_set_lemma)(old, 0) &*& I(data, state)(0);
    {
      open atomic_integer_set_pre(my_atomic_integer_set_lemma)(0);
      open I(data, state)(old);
      state->reader_waiting = true;
      state->vcopy = 0;
      close atomic_integer_set_post(my_atomic_integer_set_lemma)(old, 0);
      close I(data, state)(0);
    }
    @*/
    //@ produce_lemma_function_pointer_chunk(my_atomic_integer_set_lemma) : atomic_integer_set_lemma(0, I(data, state))() { call();};
    //@ close atomic_integer_set_pre(my_atomic_integer_set_lemma)(0);
    atomic_integer_set(x, 0);
    //@ open atomic_integer_set_post(my_atomic_integer_set_lemma)(_, 0);
  }
}

struct producer_info {
  int* x;
  int* data;
  /* ghost */ struct state* state;
};

/*@
predicate_family_instance thread_run_data(producer)(struct producer_info* info) =
  info->x |-> ?x &*& info->data |-> ?data &*& info->state |-> ?state &*& malloc_block_producer_info(info) &*&
  [1/2]atomic_integer(x, I(data, state)) &*& integer(data, _) &*& [1/4]state->reader_waiting |-> true &*& [1/2]state->writer_waiting |-> false &*& [1/2]state->vcopy |-> 0;
@*/

void consumer(int* x, int* data, /* ghost */ struct state* state)
  //@ requires [?f]atomic_integer(x, I(data, state)) &*& [1/4]state->reader_waiting |-> true;
  //@ ensures false;
{
  while(true)
    //@ invariant [f]atomic_integer(x, I(data, state)) &*& [1/4]state->reader_waiting |-> true;
  {
    consume(x, data, state);
  }
}


void producer(struct producer_info* info) //@: thread_run
  //@ requires thread_run_data(producer)(info);
  //@ ensures true;
{
  //@ open thread_run_data(producer)(info);
  int* x = info->x;
  int* data = info->data;
  /* ghost */ struct state* state = info->state;
  free(info);
  while(true)
    //@ invariant [?f]atomic_integer(x, I(data, state)) &*& integer(data, _) &*& [1/4]state->reader_waiting |-> true &*& [1/2]state->writer_waiting |-> false &*& [1/2]state->vcopy |-> 0;
  {
    produce(x, data, state);
  }
}

int main() 
  //@ requires true;
  //@ ensures true;
{
  int x = 0;
  int data = 0;
  struct state* state = malloc(sizeof(struct state)); // ghost malloc
  if(state == 0) return 0;
  //@ state->writer_waiting = false;
  //@ state->reader_waiting = true;
  //@ state->vcopy = 0;
  //@ close I(&data, state)(0);
  //@ create_atomic_integer(&x, I(&data, state));
  struct producer_info* info = malloc(sizeof(struct producer_info));
  if(info == 0) abort(); 
  info->x = &x;
  info->data = &data;
  info->state = state;
  //@ close thread_run_data(producer)(info);
  thread_start(producer, info);
  consumer(&x, &data, state);
  return 0;
}