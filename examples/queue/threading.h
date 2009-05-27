#ifndef THREADING_H
#define THREADING_H

/*@

predicate_family thread_run_pre(void *thread_run)(void *data, any info);
predicate_family thread_run_post(void *thread_run)(void *data, any info);

@*/

typedef void thread_run(void *data);
    //@ requires thread_run_pre(this)(data, ?info);
    //@ ensures thread_run_post(this)(data, info);

struct thread;

/*@
predicate thread(struct thread *thread, void *thread_run, void *data, any info);
@*/

struct thread *thread_start(void *run, void *data);
    //@ requires is_thread_run(run) == true &*& thread_run_pre(run)(data, ?info);
    //@ ensures thread(result, run, data, info);
    
void thread_join(struct thread *thread);
    //@ requires thread(thread, ?run, ?data, ?info);
    //@ ensures thread_run_post(run)(data, info);

#endif