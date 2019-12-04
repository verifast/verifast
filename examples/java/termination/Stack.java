class Node {

    Object value;
    Node next;

    Node(Object value, Node next)
        //@ requires true;
        //@ ensures this.value |-> value &*& [_]this.next |-> next;
        //@ terminates;
    {
        this.value = value;
        this.next = next;
        //@ leak this.next |-> _;
    }

}

class StackHelper {

    static void pushIter(Stack stack, Object value)
        //@ requires [_]stack.valid(call_perm_scope_of(currentThread)) &*& call_perms_omega(currentThread, {StackHelper.class});
        //@ ensures true;
        //@ terminates;
    {
        //@ int scope = call_perm_scope_of(currentThread);
        Node head;
        {
            /*@
            predicate pre() = true;
            predicate post(Object result) = [_]stack.readers |-> ?readers &*& GhostBagHandle(readers, result);
            lemma void get()
                requires Stack_spaceInv(scope, stack)(?o) &*& pre();
                ensures Stack_spaceInv(scope, stack)(o) &*& post(o);
            {
                open Stack_spaceInv(scope, stack)(o);
                open pre();
                
                GhostBag_add(stack.readers, o);
                
                close Stack_spaceInv(scope, stack)(o);
                close post(o);
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(get) : AtomicReference_get(Stack_spaceInv(scope, stack), pre, post)() { call(); };
            //@ close pre();
            head = (Node)stack.head.get();
            //@ open post(head);
        }
        Node n = new Node(value, head);
        boolean casResult;
        //@ int pushThread = currentThread;
        {
            /*@
            predicate pre() = [_]stack.readers |-> ?readers &*& GhostBagHandle(readers, head) &*& call_perms_omega(pushThread, {StackHelper.class}) &*& n.value |-> value &*& [_]n.next |-> head;
            predicate post(boolean result) = result ? true : call_perm(pushThread, {StackHelper.class}) &*& call_perms_omega(pushThread, {StackHelper.class});
            lemma void compareAndSet()
                requires Stack_spaceInv(scope, stack)(?o) &*& pre();
                ensures Stack_spaceInv(scope, stack)(o != head ? o : n) &*& post(o == head);
            {
                open Stack_spaceInv(scope, stack)(o);
                open pre();
                
                assert GhostBag(_, ?oldRs);
                GhostBag_remove(stack.readers, head);
                assert GhostBag(_, ?newRs);
                
                if (o == head) {
                    open call_perms_omega(_, _);
                    call_perm_rec_weaken(1, pair(0, count_neq<Object>(n, newRs)));
                    close call_perms(pushThread, count_neq<Object>(n, newRs), {StackHelper.class});
                    close nodes(n);
                } else {
                    count_neq_remove(o, head, oldRs);
                    count_neq_nonnegative(o, newRs);
                    assert count_neq(o, newRs) == count_neq(o, oldRs) - 1;
                    open call_perms(?thread, count_neq(o, oldRs), {StackHelper.class});
                    call_perm_rec_weaken(2, pair(0, count_neq(o, newRs)));
                    close call_perms(thread, count_neq(o, newRs), {StackHelper.class});
                    call_perm_rec_elim(1);
                    call_perm_transfer(pushThread);
                }
                
                close post(o == head);
                close Stack_spaceInv(scope, stack)(o != head ? o : n);
            }
            @*/
            //@ close pre();
            //@ produce_lemma_function_pointer_chunk(compareAndSet) : AtomicReference_compareAndSet(head, n, Stack_spaceInv(scope, stack), pre, post)() { call(); };
            casResult = stack.head.compareAndSet(head, n);
            //@ open post(casResult);
        }
        if (!casResult) {
            //@ consume_call_perm_for(StackHelper.class);
            pushIter(stack, value);
        }
    }

    static Object popIter(Stack stack)
        //@ requires [_]stack.valid(call_perm_scope_of(currentThread)) &*& call_perms_omega(currentThread, {StackHelper.class});
        //@ ensures true;
        //@ terminates;
    {
        //@ int scope = call_perm_scope_of(currentThread);
        Node head;
        {
            /*@
            predicate pre() = true;
            predicate post(Object result) = [_]stack.readers |-> ?readers &*& GhostBagHandle(readers, result) &*& result == null ? true : [_]Node_next(^result, _);
            lemma void get()
                requires Stack_spaceInv(scope, stack)(?o) &*& pre();
                ensures Stack_spaceInv(scope, stack)(o) &*& post(o);
            {
                open Stack_spaceInv(scope, stack)(o);
                open pre();
                
                GhostBag_add(stack.readers, o);
                assert nodes(?h);
                open nodes(h);
                close nodes(h);
                
                close Stack_spaceInv(scope, stack)(o);
                close post(o);
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(get) : AtomicReference_get(Stack_spaceInv(scope, stack), pre, post)() { call(); };
            //@ close pre();
            head = (Node)stack.head.get();
            //@ open post(head);
        }
        if (head == null)
            return null;
        Node next = head.next;
        boolean casResult;
        //@ int popThread = currentThread;
        {
            /*@
            predicate pre() = [_]stack.readers |-> ?readers &*& GhostBagHandle(readers, head) &*& call_perms_omega(popThread, {StackHelper.class}) &*& [_]head.next |-> next;
            predicate post(boolean result) = result ? head.value |-> _ : call_perm(popThread, {StackHelper.class}) &*& call_perms_omega(popThread, {StackHelper.class});
            lemma void compareAndSet()
                requires Stack_spaceInv(scope, stack)(?o) &*& pre();
                ensures Stack_spaceInv(scope, stack)(o != head ? o : next) &*& post(o == head);
            {
                open Stack_spaceInv(scope, stack)(o);
                open pre();
                
                assert GhostBag(_, ?oldRs);
                GhostBag_remove(stack.readers, head);
                assert GhostBag(_, ?newRs);
                
                if (o == head) {
                    open call_perms_omega(_, _);
                    call_perm_rec_weaken(1, pair(0, count_neq<Object>(next, newRs)));
                    close call_perms(popThread, count_neq<Object>(next, newRs), {StackHelper.class});
                    open nodes(head);
                } else {
                    count_neq_remove(o, head, oldRs);
                    count_neq_nonnegative(o, newRs);
                    assert count_neq(o, newRs) == count_neq(o, oldRs) - 1;
                    open call_perms(?thread, count_neq(o, oldRs), {StackHelper.class});
                    call_perm_rec_weaken(2, pair(0, count_neq(o, newRs)));
                    close call_perms(thread, count_neq(o, newRs), {StackHelper.class});
                    call_perm_rec_elim(1);
                    call_perm_transfer(popThread);
                }
                
                close post(o == head);
                close Stack_spaceInv(scope, stack)(o != head ? o : next);
            }
            @*/
            //@ close pre();
            //@ produce_lemma_function_pointer_chunk(compareAndSet) : AtomicReference_compareAndSet(head, next, Stack_spaceInv(scope, stack), pre, post)() { call(); };
            casResult = stack.head.compareAndSet(head, head.next);
            //@ open post(casResult);
        }
        if (!casResult) {
            //@ consume_call_perm_for(StackHelper.class);
            return popIter(stack);
        }
        return head.value;
    }

}

/*@

predicate nodes(Node n;) =
    n == null ?
        true
    :
        n.value |-> _ &*& [_]n.next |-> ?next &*& nodes(next);

fixpoint int count_neq<t>(t x, list<t> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x0, xs0): return (x0 != x ? 1 : 0) + count_neq(x, xs0);
    }
}

lemma_auto void count_neq_nonnegative<t>(t x, list<t> xs)
    requires true;
    ensures 0 <= count_neq(x, xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {} else {}
            count_neq_nonnegative(x, xs0);
    }
}

lemma void count_neq_remove<t>(t y, t x, list<t> xs)
    requires mem(x, xs) == true &*& y != x;
    ensures count_neq(y, remove(x, xs)) + 1 == count_neq(y, xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {} else {
                count_neq_remove(y, x, xs0);
            }
    }
}

predicate call_perms(int thread, int count, list<Class> level) = call_perm_rec(thread, level, (pair_lt)(int_lt, int_lt), pair(0, count));
predicate call_perms_omega(int thread, list<Class> level) = call_perm_rec(thread, level, (pair_lt)(int_lt, int_lt), pair(1, 0));

predicate_ctor Stack_spaceInv(int scope, Stack stack)(Object value) =
    nodes(^value) &*& [_]stack.readers |-> ?readers &*& GhostBag(readers, ?rs) &*&
    call_perms(?thread, count_neq(value, rs), {StackHelper.class}) &*& call_perm_scope_of(thread) == scope;

@*/

final class Stack {

    //@ int callPermScope;
    AtomicReference head;
    //@ int readers;
    
    //@ predicate valid(int callPermScope) = this.callPermScope |-> callPermScope &*& head |-> ?head &*& [_]head.valid(Stack_spaceInv(callPermScope, this));

    Stack()
        //@ requires true;
        //@ ensures [_]valid(call_perm_scope_of(currentThread));
        //@ terminates;
    {
        //@ callPermScope = call_perm_scope_of(currentThread);
        //@ readers = GhostBag_create();
        //@ close nodes(null);
        //@ produce_call_below_perm_();
        //@ is_wf_int_lt();
        //@ is_wf_pair_lt(int_lt, int_lt);
        //@ call_below_perm__elim_rec(1, {StackHelper.class}, (pair_lt)(int_lt, int_lt), pair(0, 0));
        //@ close call_perms(currentThread, 0, {StackHelper.class});
        //@ close Stack_spaceInv(call_perm_scope_of(currentThread), this)(null);
        //@ close exists(Stack_spaceInv(call_perm_scope_of(currentThread), this));
        head = new AtomicReference(null);
    }

    void push(Object value)
        //@ requires [_]valid(call_perm_scope_of(currentThread));
        //@ ensures true;
        //@ terminates;
    {
        //@ produce_call_below_perm_();
        //@ is_wf_int_lt();
        //@ is_wf_pair_lt(int_lt, int_lt);
        //@ call_below_perm__elim_rec(1, {StackHelper.class}, (pair_lt)(int_lt, int_lt), pair(1, 0));
        //@ close call_perms_omega(currentThread, {StackHelper.class});
        StackHelper.pushIter(this, value);
    }

    Object pop()
        //@ requires [_]valid(call_perm_scope_of(currentThread));
        //@ ensures true;
        //@ terminates;
    {
        //@ produce_call_below_perm_();
        //@ is_wf_int_lt();
        //@ is_wf_pair_lt(int_lt, int_lt);
        //@ call_below_perm__elim_rec(1, {StackHelper.class}, (pair_lt)(int_lt, int_lt), pair(1, 0));
        //@ close call_perms_omega(currentThread, {StackHelper.class});
        return StackHelper.popIter(this);
    }

}

final class Pusher implements JoinableForkee {

    static void push(Stack stack)
        //@ requires [_]stack.valid(call_perm_scope_of(currentThread));
        //@ ensures true;
        //@ terminates;
    {
        for (int i = 0; i < 10; i++)
            //@ invariant [_]stack.valid(call_perm_scope_of(currentThread));
            //@ decreases 10 - i;
        {
            stack.push((Object)Integer.valueOf(i));
        }
    }

    //@ int callPermScope;
    Stack stack;
    
    //@ predicate pre(int callPermScope, pair<list<Class>, real> waitLevel, list<Object> O) = this.callPermScope |-> callPermScope &*& O == nil &*& waitLevel == pair({Pusher.class}, 0r) &*& stack |-> ?stack &*& [_]stack.valid(callPermScope);
    //@ predicate post() = true;
    
    Pusher(Stack stack)
        //@ requires true;
        //@ ensures this.callPermScope |-> call_perm_scope_of(currentThread) &*& this.stack |-> stack;
        //@ terminates;
    {
        //@ this.callPermScope = call_perm_scope_of(currentThread);
        this.stack = stack;
    }
    
    void run()
        //@ requires obs(cons(?thisThread, ?O)) &*& pre(call_perm_scope_of(currentThread), wait_level_of(thisThread), O);
        //@ ensures obs({thisThread}) &*& post();
        //@ terminates;
    {
        push(stack);
        //@ close post();
    }
    
}

final class Popper implements JoinableForkee {

    static void pop(Stack stack)
        //@ requires [_]stack.valid(call_perm_scope_of(currentThread));
        //@ ensures true;
        //@ terminates;
    {
        for (int i = 0; i < 10; i++)
            //@ invariant [_]stack.valid(call_perm_scope_of(currentThread));
            //@ decreases 10 - i;
        {
            stack.pop();
        }
    }
    
    //@ int callPermScope;
    Stack stack;
    
    //@ predicate pre(int callPermScope, pair<list<Class>, real> waitLevel, list<Object> O) = this.callPermScope |-> callPermScope &*& O == nil &*& waitLevel == pair({Popper.class}, 0r) &*& stack |-> ?stack &*& [_]stack.valid(callPermScope);
    //@ predicate post() = true;
    
    Popper(Stack stack)
        //@ requires true;
        //@ ensures this.callPermScope |-> call_perm_scope_of(currentThread) &*& this.stack |-> stack;
        //@ terminates;
    {
        //@ this.callPermScope = call_perm_scope_of(currentThread);
        this.stack = stack;
    }
    
    void run()
        //@ requires obs(cons(?thisThread, ?O)) &*& pre(call_perm_scope_of(currentThread), wait_level_of(thisThread), O);
        //@ ensures obs({thisThread}) &*& post();
        //@ terminates;
    {
        pop(stack);
        //@ close post();
    }
    
}

class Main {

    static void main()
        //@ requires obs(nil); // For clarity, unlike examples SqrtCached and ThreadPool, this example does not apply the modular obligations specification approach.
        //@ ensures obs(nil);
        //@ terminates;
    {
        Stack stack = new Stack();
        
        //@ produce_call_below_perm_();
        //@ call_below_perm__elim(2, {Pusher.class, Popper.class});
        
        //@ close exists(nil);
        //@ call_perm_weaken(1, {Pusher.class});
        Thread pusherThread = ThreadUtil.forkJoinable(new Pusher(stack));
        Pusher.push(stack);
        pusherThread.join();
        
        //@ close exists(nil);
        //@ call_perm_weaken(1, {Popper.class});
        Thread popperThread = ThreadUtil.forkJoinable(new Popper(stack));
        Popper.pop(stack);
        popperThread.join();
    }
    
}