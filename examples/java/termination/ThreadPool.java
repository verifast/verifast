//@ predicate Task(Task task, list<Class> level;) = task.valid(?level0) &*& level_le({task.getClass()}, level0) && level_le(level0, level);

interface Task {

    //@ predicate valid(list<Class> level);
    
    void run();
        //@ requires obs(?O) &*& valid(?level) &*& call_perm(currentThread, level) &*& wait_level_below_obs(pair(level, 0r), O) == true;
        //@ ensures obs(O);
        //@ terminates;
    
}

//@ predicate Item(Item item, int scope) = item.validItem(scope) &*& level_le({item.getClass()}, {ShutdownItem.class}) == true;

interface Item {

    //@ predicate validItem(int scope);
    
    void run();
        //@ requires obs(nil) &*& validItem(call_perm_scope_of(currentThread));
        //@ ensures obs(nil);
        //@ terminates;
    
}

class ThreadPoolHelper {

    static void work(ThreadPool pool)
        //@ requires obs(nil) &*& [_]pool.valid(call_perm_scope_of(currentThread), _) &*& [_]pool.channel |-> ?channel &*& channel.credit() &*& call_perm(currentThread, {ShutdownItem.class});
        //@ ensures obs(nil);
        //@ terminates;
    {
        //@ open [_]pool.valid(_, ?O);
        Item item = (Item)pool.channel.receive();
        //@ open ThreadPool_inv(call_perm_scope_of(currentThread))(item);
        //@ open Item(item, call_perm_scope_of(currentThread));
        //@ consume_call_perm_for(item.getClass());
        item.run();
    }
    
}

final class TaskItem implements Item {

    //@ int thread;
    ThreadPool pool;
    Task task;
    //@ list<Class> taskLevel;
    
    //@ predicate validItem(int scope) = this.thread |-> ?thread &*& pool |-> ?pool &*& [_]pool.valid(scope, _) &*& [_]pool.channel |-> ?channel &*& channel.credit() &*& task |-> ?task &*& taskLevel |-> ?taskLevel &*& Task(task, taskLevel) &*& call_perm(thread, append({TaskItem.class, ShutdownItem.class}, taskLevel)) &*& call_perm_scope_of(thread) == scope;

    TaskItem(ThreadPool pool, Task task)
        //@ requires true;
        //@ ensures this.thread |-> _ &*& this.pool |-> pool &*& this.task |-> task &*& this.taskLevel |-> _;
        //@ terminates;
    {
        this.pool = pool;
        this.task = task;
    }
    
    void run()
        //@ requires obs(nil) &*& validItem(call_perm_scope_of(currentThread));
        //@ ensures obs(nil);
        //@ terminates;
    {
        //@ open validItem(_);
        //@ call_perm_transfer(currentThread);
        //@ call_perm_weaken_and_dup(3);
        //@ open Task(_, _);
        Task task = task;
        //@ assert task.valid(?taskLevel0);
        //@ level_le_trans({task.getClass()}, taskLevel0, taskLevel);
        //@ level_lt_cons(ShutdownItem.class, taskLevel);
        //@ level_le_trans({task.getClass()}, taskLevel, cons(ShutdownItem.class, taskLevel));
        //@ consume_call_perm_for(task.getClass());
        //@ call_perm_weaken_and_dup(1);
        //@ call_perm_weaken(1, taskLevel0);
        task.run();
        //@ call_perm_weaken(1, {ShutdownItem.class});
        ThreadPoolHelper.work(pool);
    }
    
}

final class ShutdownItem implements Item {

    //@ int scope;
    //@ predicate validItem(int scope) = this.scope |-> scope;
    
    void run()
        //@ requires obs(nil) &*& validItem(_);
        //@ ensures obs(nil);
        //@ terminates;
    {
    }
    
}

final class ThreadPoolWorker implements Forkee {

    ThreadPool pool;

    //@ predicate pre(int scope, list<Object> O) = O == nil &*& pool |-> ?pool &*& [_]pool.valid(scope, _) &*& [_]pool.channel |-> ?channel &*& channel.credit();
    
    ThreadPoolWorker(ThreadPool pool)
        //@ requires true;
        //@ ensures this.pool |-> pool;
        //@ terminates;
    {
        this.pool = pool;
    }
    
    void run()
        //@ requires pre(call_perm_scope_of(currentThread), ?O) &*& obs(O);
        //@ ensures obs(nil);
        //@ terminates;
    {
        //@ produce_call_below_perm_();
        //@ call_below_perm__elim(1, {ShutdownItem.class});
        ThreadPoolHelper.work(pool);
    }
    
}

//@ predicate wait_level_range(list<Class> termLevel, real a, real b) = a < b;

//@ predicate_ctor ThreadPool_inv(int scope)(Object object) = Item(^object, scope);

//@ fixpoint boolean object_wait_level_within_range(list<Class> termLevel, real a, real b, Object object) { return fst(wait_level_of(object)) == termLevel && a < snd(wait_level_of(object)) && snd(wait_level_of(object)) < b; }

//@ fixpoint boolean object_wait_levels_within_range(list<Class> termLevel, real a, real b, list<Object> O) { return forall(O, (object_wait_level_within_range)(termLevel, a, b)); }

/*@

lemma void wait_level_below_object_wait_levels_within_range(list<Class> termLevel, real a, real b, list<Object> O)
    requires object_wait_levels_within_range(termLevel, a, b, O) == true;
    ensures wait_level_below_obs(pair(termLevel, a), O) == true;
{
    if (!wait_level_below_obs(pair(termLevel, a), O)) {
        Object o = not_forall(O, (wait_level_below_object)(pair(termLevel, a)));
        forall_elim(O, (object_wait_level_within_range)(termLevel, a, b), o);
        assert false;
    }
}

@*/

final class ThreadPool {

    //@ int callPermScope;
    Channel channel;

    //@ predicate valid(int callPermScope, list<Object> O) = [_]this.callPermScope |-> callPermScope &*& channel |-> ?channel &*& [_]channel.channel(ThreadPool_inv(callPermScope)) &*& O == {channel};
    
    public ThreadPool()
        //@ requires obs(?O) &*& wait_level_below_obs(pair({ThreadPool.class}, 0r), O) == true &*& wait_level_range(?termLevel, ?a, ?b) &*& level_lt({ThreadPool.class}, termLevel) == true;
        //@ ensures [_]valid(call_perm_scope_of(currentThread), ?Or) &*& obs(append(Or, O)) &*& object_wait_levels_within_range(termLevel, a, b, Or) == true;
        //@ terminates;
    {
        //@ open wait_level_range(_, _, _);
        //@ close exists(pair(ThreadPool_inv(call_perm_scope_of(currentThread)), pair(termLevel, (a + b) / 2)));
        channel = new Channel();
        //@ leak channel |-> _;
        //@ channel.create_obs(1);
        //@ produce_call_below_perm_();
        ThreadPoolWorker worker = new ThreadPoolWorker(this);
        //@ callPermScope = call_perm_scope_of(currentThread);
        //@ close worker.pre(call_perm_scope_of(currentThread), nil);
        //@ open repeat(_, _, _);
        //@ open repeat(_, _, _);
        //@ close exists(cons<Object>(channel, O));
        //@ produce_call_below_perm_();
        //@ call_below_perm__elim(1, {ThreadPoolWorker.class});
        ThreadUtil.fork(worker);
    }

    public void addTask(Task task)
        //@ requires obs(?O) &*& [_]valid(?scope, ?Op) &*& Task(task, ?taskLevel) &*& call_perm(?thread, cons(ThreadPool.class, taskLevel)) &*& wait_level_below_obs(pair({ThreadPool.class}, 0r), O) == true &*& call_perm_scope_of(thread) == scope;
        //@ ensures obs(O);
        //@ terminates;
    {
        TaskItem item = new TaskItem(this, task);
        //@ item.thread = thread;
        //@ item.taskLevel = taskLevel;
        //@ channel.create_obs(1);
        //@ level_append_mono_l({TaskItem.class, ShutdownItem.class}, {ThreadPool.class}, taskLevel);
        //@ call_perm_weaken(1, append({TaskItem.class, ShutdownItem.class}, taskLevel));
        //@ call_perm_transfer(thread);
        //@ close item.validItem(scope);
        //@ close Item(item, scope);
        //@ close ThreadPool_inv(scope)(item);
        channel.send(item);
        //@ open repeat(_, _, _);
        //@ open repeat(_, _, _);
        //@ channel.destroy_ob();
    }

    public void shutDown()
        //@ requires [_]valid(?scope, ?Op) &*& exists<list<Object> >(?O) &*& obs(append(Op, O)) &*& wait_level_below_obs(pair({ThreadPool.class}, 0r), append(Op, O)) == true;
        //@ ensures obs(O);
        //@ terminates;
    {
        ShutdownItem item = new ShutdownItem();
        //@ item.scope = scope;
        //@ close item.validItem(scope);
        //@ close Item(item, scope);
        //@ close ThreadPool_inv(scope)(item);
        channel.send(item);
        //@ channel.destroy_ob();
    }
    
}

final class MyTask implements Task {

    //@ predicate valid(list<Class> level) = level == {MyTask.class};
    
    MyTask()
        //@ requires true;
        //@ ensures Task(this, {MyTask.class});
        //@ terminates;
    {
        //@ close valid({MyTask.class});
        //@ close Task(this, {MyTask.class});
    }
    
    void run()
        //@ requires obs(?O) &*& valid(?level) &*& call_perm(currentThread, level) &*& wait_level_below_obs(pair(level, 0r), O) == true;
        //@ ensures obs(O);
        //@ terminates;
    {
    }
    
}

class MyModule {

    static void doWork(ThreadPool pool)
        //@ requires obs(?O) &*& [_]pool.valid(call_perm_scope_of(currentThread), _) &*& wait_level_below_obs(pair({MyModule.class}, 0r), O) == true;
        //@ ensures obs(O);
        //@ terminates;
    {
        //@ produce_call_below_perm_();
        //@ call_below_perm__elim(2, {ThreadPool.class, MyTask.class});
        //@ wait_level_lt_below_obs(pair({ThreadPool.class}, 0r), pair({MyModule.class}, 0r), O);
        pool.addTask(new MyTask());
        pool.addTask(new MyTask());
    }
    
}

class Main {

    static void main()
        //@ requires obs(?O) &*& wait_level_below_obs(pair({Main.class}, 0r), O) == true;
        //@ ensures obs(O);
        //@ terminates;
    {
        //@ wait_level_lt_below_obs(pair({ThreadPool.class}, 0r), pair({Main.class}, 0r), O);
        //@ close wait_level_range({Main.class}, -1, 0);
        ThreadPool pool = new ThreadPool();
        //@ assert [_]pool.valid(call_perm_scope_of(currentThread), ?Op);
        //@ wait_level_lt_below_obs(pair({MyModule.class}, 0r), pair({Main.class}, 0r), O);
        //@ wait_level_below_object_wait_levels_within_range({Main.class}, -1, 0, Op);
        //@ wait_level_lt_below_obs(pair({MyModule.class}, 0r), pair({Main.class}, -1r), Op);
        //@ forall_append(Op, O, (wait_level_below_object)(pair({MyModule.class}, 0r)));
        MyModule.doWork(pool);
        //@ close exists(O);
        //@ wait_level_lt_below_obs(pair({ThreadPool.class}, 0r), pair({Main.class}, -1r), Op);
        //@ forall_append(Op, O, (wait_level_below_object)(pair({ThreadPool.class}, 0r)));
        pool.shutDown();
    }
    
}
