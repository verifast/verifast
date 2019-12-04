class Counter {
    int n;
    Lock lock;

    Counter()
        //@ requires exists<real>(?w);
        //@ ensures Counter(this, pair(nil, w));
        //@ terminates;
    {
        //@ close Counter_inv(this)();
        //@ close exists<predicate()>(Counter_inv(this));
        //@ close exists<pair<list<Class>, real> >(pair(nil, w));
        lock = new Lock();
    }
}

/*@

predicate_ctor Counter_inv(Counter c)(;) = c.n |-> _;

predicate Counter(Counter c; pair<list<Class>, real> waitLevel) =
    c.lock |-> ?lock &*& lock.lock(Counter_inv(c)) &*& waitLevel == wait_level_of(lock);

@*/

class Philosopher implements JoinableForkee {
    //@ int callPermScope;
    final Counter first, second;

    /*@
    predicate pre(int callPermScope, pair<list<Class>, real> waitLevel, list<Object> O) =
        [_]this.callPermScope |-> callPermScope &*&
        waitLevel == pair(nil, 4r) &*&
        [_]first |-> ?first &*& [1/2]Counter(first, ?wFirst) &*&
        [_]second |-> ?second &*& [1/2]Counter(second, ?wSecond) &*&
        O == nil &*&
        wait_level_lt(wFirst, waitLevel) && wait_level_lt(wSecond, wFirst);
    
    predicate post() =
        [_]first |-> ?first &*& [1/2]Counter(first, ?wFirst) &*&
        [_]second |-> ?second &*& [1/2]Counter(second, ?wSecond);
    @*/
    
    Philosopher(Counter first, Counter second)
        //@ requires true;
        //@ ensures [_]this.callPermScope |-> call_perm_scope_of(currentThread) &*& [_]this.first |-> first &*& [_]this.second |-> second;
        //@ terminates;
    {
        //@ this.callPermScope = call_perm_scope_of(currentThread);
        this.first = first;
        this.second = second;
    }
    
    void run()
        //@ requires obs(cons(?thisThread, ?O)) &*& pre(call_perm_scope_of(currentThread), wait_level_of(thisThread), O);
        //@ ensures obs({thisThread}) &*& post();
        //@ terminates;
    {
        first.lock.acquire();
        //@ Lock firstLock = first.lock;
        //@ open Counter_inv(first)();
        first.n++;
        //@ wait_level_lt_trans(wait_level_of(second.lock), wait_level_of(first.lock), wait_level_of(thisThread));
        second.lock.acquire();
        //@ open Counter_inv(second)();
        second.n++;
        //@ close Counter_inv(second)();
        second.lock.release();
        //@ close Counter_inv(first)();
        first.lock.release();
    }
}

class Dining {
    static void main()
        //@ requires obs(nil);
        //@ ensures obs(nil);
        //@ terminates;
    {
        //@ produce_call_below_perm_();
        //@ call_below_perm__elim(3, {Philosopher.class});
        
        //@ close exists(1r);
        Counter c1 = new Counter();
        //@ close exists(2r);
        Counter c2 = new Counter();
        //@ close exists(3r);
        Counter c3 = new Counter();

        //@ close exists(nil);
        Philosopher philo1 = new Philosopher(c2, c1);
        Thread thread1 = ThreadUtil.forkJoinable(philo1);
        //@ close exists(nil);
        Philosopher philo2 = new Philosopher(c3, c2);
        Thread thread2 = ThreadUtil.forkJoinable(philo2);
        //@ close exists(nil);
        Philosopher philo3 = new Philosopher(c3, c1);
        Thread thread3 = ThreadUtil.forkJoinable(philo3);

        thread1.join();
        thread2.join();
        thread3.join();
        
        //@ open philo1.post();
        //@ open philo2.post();
        //@ open philo3.post();
        
        //@ c1.lock.destroy();
        //@ c2.lock.destroy();
        //@ c3.lock.destroy();
        int total = c1.n + c2.n + c3.n;
    }
}
