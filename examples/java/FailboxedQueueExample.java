// Provably live exception handling with failboxes

//@ inductive level = level(real r);
//@ fixpoint boolean level_below_all(level l, list<level> ls) { return ls == nil; }

//@ fixpoint boolean subbag<t>(list<t> xs, list<t> ys) { return length(remove_all(xs, ys)) + length(xs) == length(ys); }

//@ predicate obligations(int threadId, list<level> outerObligations, Failbox failbox, list<level> obligations);

interface FailboxedBlock {
    //@ predicate pre(int thread, list<level> outerObligations, Failbox failbox);
    //@ predicate post();
    void run();
        //@ requires pre(currentThread, ?obs, ?failbox) &*& obligations(currentThread, obs, failbox, nil);
        //@ ensures post() &*& obligations(currentThread, obs, failbox, nil);
}

class Failbox {
    public Failbox()
        //@ requires true;
        //@ ensures true;
    {
    }
    public void enter(FailboxedBlock block)
        //@ requires obligations(currentThread, ?outerObs, ?outerFailbox, ?obs) &*& block.pre(currentThread, append(outerObs, obs), this);
        //@ ensures obligations(currentThread, outerObs, outerFailbox, obs) &*& block.post();
    {
        //@ assume(false);
    }
}

class LinkedBlockingQueue {
    //@ predicate LinkedBlockingQueue(Failbox failbox, level level, predicate(Object) inv);
    //@ predicate credit();
    //@ predicate debit();
    public LinkedBlockingQueue()
        //@ requires exists<Failbox>(?failbox) &*& exists<level>(?level) &*& exists<predicate(Object)>(?inv);
        //@ ensures [_]LinkedBlockingQueue(failbox, level, inv);
    {
        //@ assume(false);
    }
    public void put(Object element) throws InterruptedException /*@ ensures true; @*/
        //@ requires [_]LinkedBlockingQueue(?failbox, ?level, ?inv) &*& inv(element);
        //@ ensures credit();
    {
        //@ assume(false);
    }
    public Object take() throws InterruptedException /*@ ensures true; @*/
        //@ requires obligations(currentThread, ?outerObs, ?failbox, ?obs) &*& [_]LinkedBlockingQueue(failbox, ?level, ?inv) &*& credit() &*& level_below_all(level, append(outerObs, obs)) == true;
        //@ ensures obligations(currentThread, outerObs, failbox, obs) &*& inv(result);
    {
        //@ assume(false);
    }
    /*@
    lemma void createDebit()
        requires [_]LinkedBlockingQueue(?failbox, ?level, ?inv) &*& obligations(currentThread, ?outerObs, failbox, ?obs);
        ensures obligations(currentThread, outerObs, failbox, cons(level, obs)) &*& credit() &*& debit();
    {
        assume(false);
    }
    lemma void destroyDebit()
        requires
            [_]LinkedBlockingQueue(?failbox, ?level, ?inv) &*&
            obligations(currentThread, ?outerObs, failbox, ?obs) &*& mem(level, obs) == true &*&
            debit() &*& credit();
        ensures obligations(currentThread, outerObs, failbox, remove(level, obs));
    {
        assume(false);
    }
    @*/
}

/*

We assume that if a failbox fb fails, eventually all threads running in fb either have their interrupted flag set, or they are propagating an exception.
(TODO: It seems that this assumption holds only if we do not allow user code to call Thread.interrupted() or to catch InterruptedException. (Note: it is fine to
catch exceptions provided code then forgets that it is inside a failbox. Or, perhaps easier to achieve: disallow try-catch statements when currentFailbox != null.
Instead, enterCatch calls have to be used in that case.))
It follows that blocking calls inside fb will throw an InterruptedException.

*/

interface FailboxedRunnable {
    //@ predicate pre(Failbox failbox, list<level> obligations);
    void run();
        //@ requires pre(?failbox, ?obs) &*& obligations(currentThread, nil, failbox, obs);
        //@ ensures obligations(currentThread, nil, failbox, nil);
}

class FailboxedThread {
    //@ predicate FailboxedThread(Failbox failbox, list<level> obligations);
    public FailboxedThread(FailboxedRunnable runnable)
        //@ requires obligations(currentThread, ?outerObs, ?failbox, ?obs) &*& runnable.pre(failbox, ?rObs);
        //@ ensures obligations(currentThread, outerObs, failbox, obs) &*& FailboxedThread(failbox, rObs);
    {
        //@ assume(false);
    }
    public void start()
        /*@
        requires
            FailboxedThread(?failbox, ?thisObs) &*&
            obligations(currentThread, ?outerObs, failbox, ?obs) &*& subbag(thisObs, obs) == true;
        @*/
        //@ ensures obligations(currentThread, outerObs, failbox, remove_all(thisObs, obs));
    {
        //@ assume(false);
    }
}

//@ predicate queue_inv(Object o) = true;

class MyFailboxedRunnable implements FailboxedRunnable {
    LinkedBlockingQueue queue;
    //@ predicate pre(Failbox fb, list<level> obs) = this.queue |-> ?queue &*& [_]queue.LinkedBlockingQueue(?failbox, ?level, queue_inv) &*& fb == failbox &*& obs == {level} &*& queue.debit();
    MyFailboxedRunnable(LinkedBlockingQueue queue)
        //@ requires [_]queue.LinkedBlockingQueue(?failbox, ?level, queue_inv) &*& queue.debit();
        //@ ensures pre(failbox, {level});
    {
        this.queue = queue;
    }
    public void run()
        //@ requires pre(?failbox, ?obs) &*& obligations(currentThread, nil, failbox, obs);
        //@ ensures obligations(currentThread, nil, failbox, nil);
    {
        try {
            String hello = "hello";
            //@ close queue_inv(hello);
            queue.put(hello);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        //@ queue.destroyDebit();
    }
}

class MyFailboxedBlock implements FailboxedBlock {
    //@ int threadId;
    //@ Failbox failbox;
    //@ predicate pre(int threadId, list<level> outerObs, Failbox fb) = outerObs == nil &*& this.threadId |-> threadId &*& this.failbox |-> fb;
    //@ predicate post() = true;
    MyFailboxedBlock()
        //@ requires exists<Failbox>(?failbox);
        //@ ensures pre(currentThread, nil, failbox);
    {
        //@ this.threadId = currentThread;
        //@ this.failbox = failbox;
    }
    public void run()
        //@ requires pre(currentThread, ?obs, ?failbox) &*& obligations(currentThread, obs, failbox, nil);
        //@ ensures post() &*& obligations(currentThread, obs, failbox, nil);
    {
        //@ open pre(_, _, _);
        //@ close exists<Failbox>(failbox);
        //@ level level = level(0);
        //@ close exists<level>(level);
        //@ close exists<predicate(Object)>(queue_inv);
        LinkedBlockingQueue queue = new LinkedBlockingQueue();
        //@ queue.createDebit();
        new FailboxedThread(new MyFailboxedRunnable(queue)).start();
        try {
            queue.take();
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        //@ close post();
    }
}

class QueueExample {
    public static void main(String[] args)
        //@ requires obligations(currentThread, nil, null, nil);
        //@ ensures obligations(currentThread, nil, null, nil);
    {
        Failbox failbox = new Failbox();
        //@ close exists(failbox);
        failbox.enter(new MyFailboxedBlock());
    }
}
