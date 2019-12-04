//@ predicate True(Object element) = true;

class Consumer implements Forkee {
    //@ int callPermScope;
    Channel c;
    
    //@ predicate pre(int callPermScope, list<Object> O) = this.callPermScope |-> callPermScope &*& c |-> ?c &*& [_]c.channel(True) &*& credits(c, 10) &*& O == nil;
    
    void run()
        //@ requires obs(?O) &*& pre(call_perm_scope_of(currentThread), O);
        //@ ensures obs(nil);
        //@ terminates;
    {
        //@ open pre(_, O);
        Channel c = c;
        for (int i = 0; i < 10; i++)
            //@ invariant obs(nil) &*& [_]c.channel(True) &*& credits(c, 10 - i);
            //@ decreases 10 - i;
        {
            c.receive();
        }
    }

}

class ProdCons {
    static void main()
        //@ requires obs(nil);
        //@ ensures obs(nil);
        //@ terminates;
    {
        //@ produce_call_below_perm_();
        //@ call_below_perm__elim(1, {Consumer.class});
        
        //@ close exists(pair(True, pair({ProdCons.class}, 0r)));
        Channel c = new Channel();
        //@ c.create_obs(10);
        //@ assert obs(?O0);
        Consumer cons = new Consumer();
        //@ cons.callPermScope = call_perm_scope_of(currentThread);
        cons.c = c;
        //@ close cons.pre(_, nil);
        //@ close exists(O0);
        ThreadUtil.fork(cons);

        for (int i = 0; i < 10; i++)
            //@ invariant repeat<Object>(c, 10 - i, ?O) &*& obs(O) &*& [_]c.channel(True);
            //@ decreases 10 - i;
        {
            //@ close True(null);
            c.send(null);
            //@ open repeat(_, _, _);
            //@ c.destroy_ob();
        }
        //@ open repeat(_, _, _);
    }
}
