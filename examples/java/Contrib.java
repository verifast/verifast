import java.util.concurrent.*;
import verifast.*;

class Counter {
    
    int value;
    //@ int c1;
    //@ int c2;
    
}

/*@

predicate_ctor Counter(Counter counter)() =
    counter.value |-> ?value
    &*& [1/2]counter.c1 |-> ?v1
    &*& [1/2]counter.c2 |-> ?v2
    &*& value == v1 + v2;

@*/

final class Session1 implements Runnable {
    
    Counter counter;
    Semaphore lock;
    
    //@ predicate pre() = [1/2]counter |-> ?c &*& [1/2]lock |-> ?l &*& semaphore_handle(l, Counter(c), 1/3, 0) &*& [1/2]c.c1 |-> 0;
    //@ predicate post() = [1/2]counter |-> ?c &*& [1/2]lock |-> ?l &*& semaphore_handle(l, Counter(c), 1/3, 0) &*& [1/2]c.c1 |-> 1;
    
    public void run()
        //@ requires pre();
        //@ ensures post();
    {
        try {
            this.runCore();
        } catch (InterruptedException e) {
            RuntimeException e0 = new RuntimeException(e);
            throw e0;
        }
    }
    
    public void runCore() throws InterruptedException /*@ ensures true; @*/
        //@ requires pre();
        //@ ensures post();
    {
        lock.acquire();
        //@ open Counter(counter)();
        counter.value++;
        //@ counter.c1++;
        //@ close Counter(counter)();
        lock.release();
    }
    
}

final class Session2 implements Runnable {
    
    Counter counter;
    Semaphore lock;
    
    //@ predicate pre() = [1/2]counter |-> ?c &*& [1/2]lock |-> ?l &*& semaphore_handle(l, Counter(c), 1/3, 0) &*& [1/2]c.c2 |-> 0;
    //@ predicate post() = [1/2]counter |-> ?c &*& [1/2]lock |-> ?l &*& semaphore_handle(l, Counter(c), 1/3, 0) &*& [1/2]c.c2 |-> 1;
    
    public void run()
        //@ requires pre();
        //@ ensures post();
    {
        try {
            this.runCore();
        } catch (InterruptedException e) {
            RuntimeException e0 = new RuntimeException(e);
            throw e0;
        }
    }
    
    public void runCore() throws InterruptedException /*@ ensures true; @*/
        //@ requires pre();
        //@ ensures post();
    {
        lock.acquire();
        //@ open Counter(counter)();
        counter.value++;
        //@ counter.c2++;
        //@ close Counter(counter)();
        lock.release();
    }
    
}

class Program {
    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Counter c = new Counter();
        //@ close Counter(c)();
        //@ one_time(Counter(c));
        Semaphore lock = new Semaphore(1);
        //@ lock.splitHandle(1r, 1, 1r/3, 1);
        //@ lock.splitHandle(2r/3, 0, 1r/3, 0);
        
        Session1 session1 = new Session1();
        session1.counter = c;
        session1.lock = lock;
        JoinableRunnable session1Joinable = ThreadingHelper.createJoinableRunnable(session1);
        //@ close session1.pre();
        //@ session1Joinable.closeIt();
        Thread thread1 = new Thread(session1Joinable);
        thread1.start();
        
        Session2 session2 = new Session2();
        session2.counter = c;
        session2.lock = lock;
        JoinableRunnable session2Joinable = ThreadingHelper.createJoinableRunnable(session2);
        //@ close session2.pre();
        //@ session2Joinable.closeIt();
        Thread thread2 = new Thread(session2Joinable);
        thread2.start();
        
        ThreadingHelper.join(thread1, session1Joinable);
        //@ open session1.post();
        ThreadingHelper.join(thread2, session2Joinable);
        //@ open session2.post();
        
        //@ lock.mergeHandles(1r/3, 0, 1r/3, 0);
        //@ lock.mergeHandles(1r/3, 1, 2r/3, 0);
        //@ lock.destroy();
        //@ open n_times(1, Counter(c));
        //@ open Counter(c)();
        
        int sum = c.value;
        assert(sum == 2);
    }
} 