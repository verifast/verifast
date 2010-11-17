import java.util.concurrent.*;
import verifast.*;

class Counter {
    int value;
    int c1;
    int c2;
    
    Counter(int v)
        //@ requires true;
        //@ ensures this.value |-> v &*& this.c1 |-> 0 &*& this.c2 |-> 0;
    {
      this.value = v;
    }
    
    void increment()
        //@ requires this.value |-> ?v;
        //@ ensures this.value |-> v + 1;
    {
      this.value = this.value + 1;
    }
}

/*@

inductive pair<t1, t2> = pair(t1, t2);

fixpoint t1 fst<t1, t2>(pair<t1, t2> pr) {
  switch(pr) {    case pair(a, b): return a;  }}fixpoint t2 snd<t1, t2>(pair<t1, t2> pr) {
  switch(pr) {    case pair(a, b): return b;  }}
predicate_ctor Counter_ctor(Counter counter)() = counter.value |-> ?value &*& [1/2]counter.c1 |-> ?v1 
	&*& [1/2]counter.c2 |-> ?v2 &*& value == v1 + v2;
        
predicate Session(Session Session, pair<int, real> pf, int contrib) = [1/2]Session.counter |-> ?counter &*& counter != null 
	&*& [1/2]Session.lock |-> ?lock &*& lock != null &*& [1/2]Session.first |-> ?first 
	&*& (first == true ? [1/2]counter.c1 |-> contrib : [1/2]counter.c2 |-> contrib)
	&*& semaphore(snd(pf), lock, fst(pf), Counter_ctor(counter));
	
predicate_family_instance thread_run_pre(Session.class)(Session run, pair<int, real> info) = Session(run, info, 0);
predicate_family_instance thread_run_post(Session.class)(Session run, pair<int, real> info) = Session(run, info, 1);
@*/

class Session implements Runnable {
    Counter counter;
    Semaphore lock;
    boolean first;
    
    public Session(Counter c, Semaphore l, boolean first)
        //@ requires c != null;
        //@ ensures this.counter |-> c &*& this.lock |-> l &*& this.first |-> first;
    {
        this.counter = c;
        this.lock = l;
        this.first = first;
    }
    
    public void run()
        //@ requires thread_run_pre(Session.class)(this, ?info);
        //@ ensures thread_run_post(Session.class)(this, info);
    {
        try {
            this.runCore();
        } catch (InterruptedException e) {
            RuntimeException e0 = new RuntimeException(e);
            throw e0;
        }
    }
    
    public void runCore() throws InterruptedException
        //@ requires thread_run_pre(Session.class)(this, ?info);
        //@ ensures thread_run_post(Session.class)(this, info);
    {
        //@ open thread_run_pre(Session.class)(this, ?info2);
        //@ open Session(this, info2, 0);
        Semaphore lock = this.lock;
        Counter c = this.counter;
        lock.acquire();
        //@ open Counter_ctor(c)();
	c.increment();
	if(this.first) {
		c.c1 = c.c1 + 1;
	}
	else {
		c.c2 = c.c2 + 1;
	}
	//@ close Counter_ctor(c)();
        lock.release();
        //@ close Session(this, info2, 1);
        //@ close thread_run_post(Session.class)(this, info2);
    }
}

class Program {
    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Counter c = new Counter(0);
	//@ close Counter_ctor(c)();
	//@ close n_times(0, Counter_ctor(c));
	//@ close n_times(1, Counter_ctor(c));
        Semaphore lock = new Semaphore(1);	//@ semaphore_split_detailed(lock, 1/2, 1);
        Session session1 = new Session(c, lock, true);
        //@ close Session(session1, pair(0, 1/2), 0);
        //@ close thread_run_pre(Session.class)(session1, pair(0, 1/2));
        JoinableRunnable session1Joinable = ThreadingHelper.createJoinableRunnable(session1);
        //@ close_joinable_runnable(session1Joinable);
        Thread thread1 = new Thread(session1Joinable);
        thread1.start();
        Session session2 = new Session(c, lock, false);
        //@ close Session(session2, pair(1, 1/2), 0);
        //@ close thread_run_pre(Session.class)(session2, pair(1, 1/2));
        JoinableRunnable session2Joinable = ThreadingHelper.createJoinableRunnable(session2);
        //@ close_joinable_runnable(session2Joinable);
        Thread thread2 = new Thread(session2Joinable);
        thread2.start();
        ThreadingHelper.join(thread1, session1Joinable);
        //@ open thread_run_post(Session.class)(session1, pair(0, 1/2)); 
        ThreadingHelper.join(thread2, session2Joinable);
        //@ open thread_run_post(Session.class)(session2, pair(1, 1/2)); 
        //@ open Session(session1, pair(0, 1/2), 1);
        //@ open Session(session2, pair(1, 1/2), 1);
        //@ semaphore_join();
        //@ semaphore_dispose(lock);
        //@ open n_times(1, Counter_ctor(c));
        //@ open Counter_ctor(c)();
        int sum = c.value;
        assert(sum == 2);
    }
} 