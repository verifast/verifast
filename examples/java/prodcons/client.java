// Work done in collaboration with Sybren Roede and Ruurd Kuiper

import java.util.concurrent.*;
import verifast.*;

/*@

fixpoint boolean non_null(Object o) { return o != null; }

predicate_ctor client_inv(ArrayBlockingQueue queue)() =
    queue.state(?items, ?qms) &*& forall(items, non_null) == true &*&
    [1/2]Program_sendMaxCount(?smc) &*& 0 < smc &*&
    [1/2]Program_receiveMaxCount(?rmc) &*& 0 < rmc &*&
    [_]Program_producers(?s) &*&
    [_]Program_producersCount(?sc) &*&
    [1/3]array_slice_deep(s, 0, sc, producerWorkerInv, unit, _, ?lstSc)  &*&
    [_]Program_consumers(?r) &*&
    [_]Program_consumersCount(?rc) &*&
    [1/3]array_slice_deep(r, 0, rc, consumerWorkerInv, unit, _, ?lstRc) &*&
    length(items) == sum(lstSc) - sum(lstRc) &*&
    sum(lstRc) <= sum(lstSc);

predicate producerWorkerInv(unit u, ProducerThread sw; int producerCount) =
    [3/2]sw.producerSendCount |-> producerCount;

predicate consumerWorkerInv(unit u, ConsumerThread rw; int consumerCount) =
    [3/2]rw.consumerReceiveCount |-> consumerCount;

fixpoint int sum(list<int> vs) {
    switch(vs) {
      case nil: return 0;
      case cons(h, t): return h + sum(t);
    }
}

lemma_auto void sum_all_eq(list<int> vs)
    requires all_eq(vs, 0) == true;
    ensures sum(vs) == 0;
{
    switch(vs) {
        case nil :
        case cons (x0, xs0): sum_all_eq(xs0);
    }
}

lemma void sum_take_cons_drop(int k, list<int> xs, int x)
    requires 0 <= k &*& k < length(xs);
    ensures sum(xs) == sum(append(take(k, xs), cons(x, drop(k + 1, xs)))) - x + head(take(1, drop(k, xs)));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (k == 0) {
            } else {
                sum_take_cons_drop(k - 1, xs0, x);
            }
    }
}

predicate my_sep_pred() = true;

predicate_ctor my_unsep_pred(ArrayBlockingQueue queue)(list<Object> items, int qms) =
    forall(items, non_null) == true &*&
    [1/2]Program_sendMaxCount(?smc) &*&  0 < smc &*&
    [1/2]Program_receiveMaxCount(?rmc) &*& 0 < rmc &*&
    [_]Program_producers(?s) &*&
    [_]Program_producersCount(?sc) &*&
    [1/3]array_slice_deep(s, 0, sc, producerWorkerInv, unit, _, ?lstSc)  &*&
    [_]Program_consumers(?r) &*&
    [_]Program_consumersCount(?rc) &*&
    [1/3]array_slice_deep(r, 0, rc, consumerWorkerInv, unit, _, ?lstRc) &*&
    length(items) == sum(lstSc) - sum(lstRc) &*&
    sum(lstRc) <= sum(lstSc);

lemma void my_sep()
    requires exists<ArrayBlockingQueue>(?queue) &*& my_sep_pred() &*& client_inv(queue)();
    ensures queue.state(?items, ?qms) &*& my_unsep_pred(queue)(items, qms);
{
    open client_inv(queue)();
    assert queue.state(?items, ?qms);
    close my_unsep_pred(queue)(items, qms);
}

lemma void my_unsep()
    requires exists<ArrayBlockingQueue>(?queue) &*& my_unsep_pred(queue)(?items, ?qms) &*& queue.state(items, qms);
    ensures my_sep_pred() &*& client_inv(queue)();
{
    open my_unsep_pred(queue)(_, _);
    close client_inv(queue)();
    close my_sep_pred();
}

predicate foreach_i<t>(int i, list<t> xs, predicate(int, t) p) =
    switch (xs) {
        case nil: return true;
        case cons(x0, xs0): return p(i, x0) &*& foreach_i(i + 1, xs0, p);
    };

lemma void foreach_i_append<t>(int i, list<t> xs, list<t> ys)
    requires foreach_i(i, xs, ?p) &*& foreach_i(i + length(xs), ys, p);
    ensures foreach_i(i, append(xs, ys), p);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            open foreach_i(i, xs, p);
            foreach_i_append(i + 1, xs0, ys);
            close foreach_i(i, append(xs, ys), p);
    }
}

@*/

/*@

predicate producerWorker(unit u, ProducerThread ProducerWorker; unit u2) =
    [3]ProducerWorker.thread |-> ?t &*&  [3]ProducerWorker.joinable |-> ?j &*&
    [3]t.Thread(j, true) &*& [3]j.JoinableRunnable(ProducerWorker, true) &*& ProducerWorker.getClass() == ProducerThread.class &*&
    u2 == unit;

predicate producerWorkerNull(unit u, ProducerThread ProducerWorker; unit u2) =
    [3/2]ProducerWorker.thread |-> _ &*&  [3/2]ProducerWorker.joinable |-> _ &*&
    [3/2]ProducerWorker.myIndex |-> _ &*&
    ProducerWorker.getClass() == ProducerThread.class &*& [3/4]ProducerWorker.producerSendCount |-> 0 &*&
    u2 == unit;

predicate producerWorkerIndex(int i, ProducerThread t) =
    [_]t.myIndex |-> i;

@*/

class ProducerThread implements Runnable {
    
    //@ int producerSendCount;
    //@ int myIndex;
    Thread thread;
    JoinableRunnable joinable;
    
    /*@
    
    predicate pre()  =
        [_]Program_queue(?queue) &*& [_]queue.ArrayBlockingQueue() &*& [_]atomic_space(client_inv(queue)) &*&
        [_]Program_sendMaxCount(?smc) &*& 0 < smc &*&
        [_]Program_producers(?s) &*& [_]this.myIndex |-> ?myIndex &*&
        [_]Program_producersCount(?sc) &*& myIndex < sc  &*&
        [1/3]array_slice_deep(s, myIndex, myIndex + 1, producerWorkerInv, unit, cons(this, nil), cons(0, nil));
    
    predicate post() =
        [_]Program_queue(?queue) &*& [_]queue.ArrayBlockingQueue() &*& [_]atomic_space(client_inv(queue)) &*&
        [_]Program_sendMaxCount(?smc) &*&
        [_]Program_producers(?s) &*& [_]this.myIndex |-> ?myIndex &*&
        [_]Program_producersCount(?sc) &*& myIndex < sc  &*&
        [1/3]array_slice_deep(s, myIndex, myIndex + 1, producerWorkerInv, unit, cons(this, nil), cons(smc, nil));
    
    @*/
    
    public void run()
        //@ requires pre();
        //@ ensures post();
    {
        String m = "Hello";
        int i;
        for(i = 0; i < Program.sendMaxCount; i++)
            /*@
            invariant
                [_]Program_queue(?queue) &*& [_]queue.ArrayBlockingQueue() &*& [_]atomic_space(client_inv(queue)) &*&
                [_]Program_sendMaxCount(?smc) &*& i <= smc &*&
                [_]Program_producers(?s) &*& [_]this.myIndex |-> ?myIndex &*&
                [_]Program_producersCount(?sc) &*& myIndex < sc &*&
                [1/3]array_slice_deep(s, myIndex, myIndex + 1, producerWorkerInv, unit, cons(this, nil), cons(i, nil));
            @*/
        {
            /*@
            predicate P() =
                [_]Program_sendMaxCount(smc) &*&
                [_]Program_producers(s) &*& [_]this.myIndex |-> myIndex &*&
                [_]Program_producersCount(sc) &*& myIndex < sc &*&
                [1/3]array_slice_deep(s, myIndex, myIndex + 1, producerWorkerInv, unit, cons(this, nil), cons(i, nil));
            predicate Q() =
                [_]Program_sendMaxCount(smc) &*&
                [_]Program_producers(s) &*& [_]this.myIndex |-> myIndex &*&
                [_]Program_producersCount(sc) &*& myIndex < sc &*&
                [1/3]array_slice_deep(s, myIndex, myIndex + 1, producerWorkerInv, unit, cons(this, nil), cons(i + 1, nil));
            
            lemma void my_put()
                requires i < smc &*& P() &*& my_unsep_pred(queue)(?items, ?qms) &*& length(items) < qms;
                ensures Q() &*& my_unsep_pred(queue)(append(items, cons(m, nil)), qms);
            {
                open P();
                open my_unsep_pred(queue)(items, qms);
                ProducerThread[] producers = Program.producers;
                int producersCount = Program.producersCount;
                int k = myIndex;
                assert [1/3]array_slice_deep(producers, 0, producersCount, producerWorkerInv, unit, _, ?oldProducerCounts);
                array_slice_deep_split(Program.producers, 0, myIndex);
                array_slice_deep_split_precise(1/3, Program.producers, myIndex, Program.producersCount, producerWorkerInv, unit, myIndex + 1);
                array_slice_deep_open_precise(2/3, Program.producers, myIndex);
                int myOldSendCount = producerSendCount;
                producerSendCount++;
                int myNewSendCount = producerSendCount;
                array_slice_deep_close(Program.producers, myIndex, producerWorkerInv, unit);
                array_slice_deep_join_precise(1/3, Program.producers, myIndex, myIndex + 1, producerWorkerInv, unit, Program.producersCount);
                array_slice_deep_join_precise(1/3, Program.producers, 0, myIndex, producerWorkerInv, unit, Program.producersCount);
                
                forall_append(items, cons(m, nil), non_null);
                length_append(items, cons(m, nil));
                assert [1/3]array_slice_deep(producers, 0, producersCount, producerWorkerInv, unit, _, ?newProducerCounts);
                assert newProducerCounts == append(take(k, oldProducerCounts), cons(myNewSendCount, drop(1, drop(k, oldProducerCounts))));
                assert length(oldProducerCounts) == producersCount;
                assert 0 <= 1 &*& 0 <= k &*& 1 + k <= length(oldProducerCounts);
                drop_drop(1, k, oldProducerCounts);
                assert newProducerCounts == append(take(k, oldProducerCounts), cons(myNewSendCount, drop(k + 1, oldProducerCounts)));
                sum_take_cons_drop(k, oldProducerCounts, myNewSendCount);
                assert sum(newProducerCounts) == sum(oldProducerCounts) + myNewSendCount - myOldSendCount;
                close my_unsep_pred(queue)(append(items, cons(m, nil)), qms);
                close Q();
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(my_sep) : ArrayBlockingQueue_sep(client_inv(queue), queue, my_sep_pred, my_unsep_pred(queue))() { close exists(queue); call(); };
            //@ produce_lemma_function_pointer_chunk(my_unsep) : ArrayBlockingQueue_unsep(client_inv(queue), queue, my_sep_pred, my_unsep_pred(queue))() { close exists(queue); call(); };
            //@ close my_sep_pred();
            //@ produce_lemma_function_pointer_chunk(my_put) : ArrayBlockingQueue_put(client_inv(queue), queue, my_unsep_pred(queue), m, P, Q)() { call(); };
            //@ close P();
            Program.queue.put(m);
            //@ open Q();
        }
        //@ assert i == Program.sendMaxCount;
        //@ close post();
    }
}

/*@

predicate consumerWorker(unit u, ConsumerThread ConsumerWorker; unit u2) =
    [3]ConsumerWorker.thread |-> ?t &*& [3]ConsumerWorker.joinable |-> ?j &*&
    [3]t.Thread(j, true) &*& [3]j.JoinableRunnable(ConsumerWorker, true) &*& ConsumerWorker.getClass() == ConsumerThread.class &*&
    u2 == unit;

predicate consumerWorkerNull(unit u, ConsumerThread ConsumerWorker; unit u2) =
    [3/2]ConsumerWorker.thread |-> _ &*&  [3/2]ConsumerWorker.joinable |-> _ &*&
    [3/2]ConsumerWorker.myIndex |-> _ &*&
    ConsumerWorker.getClass() == ConsumerThread.class &*& [3/4]ConsumerWorker.consumerReceiveCount |-> 0 &*&
    u2 == unit;

predicate consumerWorkerIndex(int i, ConsumerThread t) =
    [_]t.myIndex |-> i;

@*/

class ConsumerThread implements Runnable {
    //@ int consumerReceiveCount;
    //@ int myIndex;
    Thread thread;
    JoinableRunnable joinable;
    
    /*@
    
    predicate pre() =
        [_]Program_queue(?queue) &*& [_]queue.ArrayBlockingQueue() &*& [_]atomic_space(client_inv(queue)) &*&
        [_]Program_receiveMaxCount(?rmc) &*& 0 < rmc &*&
        [_]Program_consumers(?s) &*& [_]this.myIndex |-> ?myIndex &*&
        [_]Program_consumersCount(?rc) &*& myIndex < rc  &*&
        [1/3]array_slice_deep(s, myIndex, myIndex + 1, consumerWorkerInv, unit, cons(this, nil), cons(0, nil));
    
    predicate post() =
        [_]Program_queue(?queue) &*& [_]queue.ArrayBlockingQueue() &*& [_]atomic_space(client_inv(queue)) &*&
        [_]Program_receiveMaxCount(?rmc) &*&
        [_]Program_consumers(?s) &*& [_]this.myIndex |-> ?myIndex &*&
        [_]Program_consumersCount(?rc) &*& myIndex < rc  &*&
        [1/3]array_slice_deep(s, myIndex, myIndex + 1, consumerWorkerInv, unit, cons(this, nil), cons(rmc, nil));
    
    @*/
    
    public void run()
        //@ requires pre();
        //@ ensures post();
    {
        int i;
        for (i=0; i < Program.receiveMaxCount; i++)
            /*@
            invariant
                [_]Program_queue(?queue) &*& [_]queue.ArrayBlockingQueue() &*& [_]atomic_space(client_inv(queue)) &*&
                [_]Program_receiveMaxCount(?rmc) &*& i <= rmc &*&
                [_]Program_consumers(?r) &*& [_]this.myIndex |-> ?myIndex &*&
                [_]Program_consumersCount(?rc) &*& myIndex < rc &*&
                [1/3]array_slice_deep(r, myIndex, myIndex + 1, consumerWorkerInv, unit, cons(this, nil), cons(i, nil));
            @*/
        {
            /*@
            predicate P() =  
                [_]Program_receiveMaxCount(rmc) &*&
                [_]Program_consumers(r) &*& [_]this.myIndex |-> myIndex &*&
                [_]Program_consumersCount(rc) &*& myIndex < rc &*&
                [1/3]array_slice_deep(r, myIndex, myIndex + 1, consumerWorkerInv, unit, cons(this, nil), cons(i, nil));
            predicate Q(Object result) = 
                [_]Program_receiveMaxCount(rmc) &*& 
                [_]Program_consumers(r) &*& [_]this.myIndex |-> myIndex &*& 
                [_]Program_consumersCount(rc) &*& myIndex < rc &*&
                [1/3]array_slice_deep(r, myIndex, myIndex + 1, consumerWorkerInv, unit, cons(this, nil), cons(i + 1, nil));
            
            lemma void my_ArrayBlockingQueue_take()
                requires i < rmc &*& P() &*& my_unsep_pred(queue)(?items, ?qms) &*& items != nil;
                ensures Q(head(items)) &*& my_unsep_pred(queue)(tail(items), qms);
            {
                open P();
                open my_unsep_pred(queue)(items, qms);
                ConsumerThread[] consumers = Program.consumers;
                int consumersCount = Program.consumersCount;
                int k = myIndex;
                assert [1/3]array_slice_deep(consumers, 0, consumersCount, consumerWorkerInv, unit, _, ?oldConsumerCounts);
                array_slice_deep_split(Program.consumers, 0, myIndex);
                array_slice_deep_split_precise(1/3, Program.consumers, myIndex, Program.consumersCount, consumerWorkerInv, unit, myIndex + 1);
                array_slice_deep_open_precise(2/3, Program.consumers, myIndex);
                int myOldReceiveCount = consumerReceiveCount;
                switch (items) {
                case nil:
                case cons(head, tail):
                    consumerReceiveCount++;
                }
                int myNewConsumerCount = consumerReceiveCount;
                array_slice_deep_close(Program.consumers, myIndex, consumerWorkerInv, unit);
                array_slice_deep_join_precise(1/3, Program.consumers, myIndex, myIndex + 1, consumerWorkerInv, unit, Program.consumersCount);
                array_slice_deep_join_precise(1/3, Program.consumers, 0, myIndex, consumerWorkerInv, unit, Program.consumersCount);
                
                assert [1/3]array_slice_deep(consumers, 0, consumersCount, consumerWorkerInv, unit, _, ?newConsumerCounts);
                assert newConsumerCounts == append(take(k, oldConsumerCounts), cons(myNewConsumerCount, drop(1, drop(k, oldConsumerCounts))));
                assert length(oldConsumerCounts) == consumersCount;
                assert 0 <= 1 &*& 0 <= k &*& 1 + k <= length(oldConsumerCounts);
                drop_drop(1, k, oldConsumerCounts);
                assert newConsumerCounts == append(take(k, oldConsumerCounts), cons(myNewConsumerCount, drop(k + 1, oldConsumerCounts)));
                sum_take_cons_drop(k, oldConsumerCounts, myNewConsumerCount);
                assert sum(newConsumerCounts) == sum(oldConsumerCounts) + myNewConsumerCount - myOldReceiveCount;
                
                switch (items) {
                case nil:
                case cons(head, tail):
                    close my_unsep_pred(queue)(tail, qms);
                    close Q(head);
                }
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(my_sep) : ArrayBlockingQueue_sep(client_inv(queue), queue, my_sep_pred, my_unsep_pred(queue))() { close exists(queue); call(); };
            //@ produce_lemma_function_pointer_chunk(my_unsep) : ArrayBlockingQueue_unsep(client_inv(queue), queue, my_sep_pred, my_unsep_pred(queue))() { close exists(queue); call(); };
            //@ close my_sep_pred();
            //@ produce_lemma_function_pointer_chunk(my_ArrayBlockingQueue_take) : ArrayBlockingQueue_take(client_inv(queue), queue, my_unsep_pred(queue), P, Q)() { call(); };
            //@ close P();
            String m = (String)Program.queue.take();
            //@ open Q(m);
        }
        //@ close post();
    }
}

class Program {
    
    //@ static int sendCount;
    //@ static int receiveCount;
    
    public static int sendMaxCount;
    public static int receiveMaxCount;
    public static ArrayBlockingQueue queue;
    public static int producersCount;
    public static int consumersCount;
    public static ProducerThread[] producers;
    public static ConsumerThread[] consumers;
    
    public static void main(String[] args)
        //@ requires class_init_token(Program.class);
        //@ ensures true;
    {
        //@ init_class();
        Program.producersCount = 1000;
        Program.consumersCount = 1000;
        Program.sendMaxCount = 2000;
        Program.receiveMaxCount = 2000;
        Program.work();
        //@assert Program.sendCount == 2000000;
        //@assert Program.receiveCount == 2000000;
    }
    
    public static void work()
        /*@
        requires
            Program_queue(_) &*&
            Program_producers(_) &*& Program_consumers(_) &*&
            [_]Program_producersCount(?producersCount) &*& [_]Program_consumersCount(?consumersCount) &*&
            0 < producersCount &*& 0 < consumersCount &*&
            Program_sendCount(?psc) &*& Program_receiveCount(?prc) &*& psc==0 &*& prc==0 &*&
            Program_sendMaxCount(?smc) &*& 0 < smc  &*& Program_receiveMaxCount(?rmc) &*& 0 < rmc;
        @*/
        //@ ensures Program_sendCount(smc * producersCount) &*& Program_receiveCount(rmc * consumersCount);
     {
        Program.producers = new ProducerThread[Program.producersCount];
        //@ ProducerThread[] s = Program.producers;
        //@ leak Program_producers(s);
        //@ array_slice_deep_empty_close(s, 0, producerWorker, unit);
        for (int i = 0; i < Program.producersCount; i++)
            /*@
            invariant
                0 <= i &*& i <= producersCount &*&
                [_]Program_producers(s) &*& [_]Program_producersCount(producersCount) &*&
                [1/3]Program_sendMaxCount(smc) &*& 0 < smc &*&
                array_slice(s, i, producersCount, ?elems) &*& all_eq(elems, null) == true &*&
                [1/3]array_slice_deep(s, 0, i, producerWorkerInv, unit, _, ?v) &*& all_eq(v, 0) == true &*&
                [2/3]array_slice_deep(s, 0, i, producerWorkerNull, unit, _, _);
            @*/
        {
            Program.producers[i] = new ProducerThread();
            //@ Program.producers[i].myIndex = i;
            //@ array_slice_split(producers, i, i + 1);
            //@ close [2/3]producerWorkerNull(unit, producers[i], unit);
            //@ close [1/3]producerWorkerInv(unit, producers[i], _);
            //@ array_slice_deep_close_precise(2/3, producers, i, producerWorkerNull, unit);
            //@ array_slice_deep_close_precise(1/3, producers, i, producerWorkerInv, unit);
            
        }
        
        Program.consumers = new ConsumerThread[Program.consumersCount];
        //@ ConsumerThread[] r = Program.consumers;
        //@ leak Program_consumers(r);
        //@ array_slice_deep_empty_close(r, 0, consumerWorker, unit);
        for (int i = 0; i < Program.consumersCount; i++)
            /*@
            invariant
                0 <= i &*& i <= consumersCount &*&
                [_]Program_consumers(r) &*& [_]Program_consumersCount(consumersCount) &*&
                [1/3]Program_receiveMaxCount(rmc) &*& 0 < rmc &*&
                array_slice(r, i, consumersCount, ?elems) &*& all_eq(elems, null) == true &*&
                [1/3]array_slice_deep(r, 0, i, consumerWorkerInv, unit, _, ?v) &*& all_eq(v, 0) == true &*&
                [2/3]array_slice_deep(r, 0, i, consumerWorkerNull, unit, _, _);
            @*/
        {
            consumers[i] = new ConsumerThread();
            //@ Program.consumers[i].myIndex = i;
            //@ array_slice_split(consumers, i, i + 1);
            //@ close [2/3]consumerWorkerNull(unit, consumers[i], unit);
            //@ close [1/3]consumerWorkerInv(unit, consumers[i], _);
            //@ array_slice_deep_close_precise(2/3, consumers, i, consumerWorkerNull, unit);
            //@ array_slice_deep_close_precise(1/3, consumers, i, consumerWorkerInv, unit);
        }
        Program.queue = new ArrayBlockingQueue(2);
        
        //@ close client_inv(Program.queue)();
        //@ create_atomic_space(client_inv(Program.queue));
        //@ close foreach_i(0, nil, producerWorkerIndex);
        
        for (int i = 0; i < Program.producersCount; i++)
            /*@
            invariant
                0 <= i &*& i <= producersCount &*&
                [_]Program_producersCount(producersCount) &*& [_]Program_producers(s) &*&
                [_]Program_queue(?queue) &*& [_]queue.ArrayBlockingQueue() &*& [_]atomic_space(client_inv(queue)) &*& [_]Program_sendMaxCount(smc) &*& 0 < smc &*&
                [2/3]array_slice_deep(s, i, producersCount, producerWorkerNull, unit, _, _) &*&
                [1/3]array_slice_deep(s, 0, i, producerWorker, unit, ?elements, _) &*& foreach_i(0, elements, producerWorkerIndex);
            @*/
        {
            //@ array_slice_deep_split(s, i, i + 1);
            //@ array_slice_deep_open_precise(2/3, s, i);
            ProducerThread producer = producers[i];
            //@ close [1/3]producerWorkerInv(unit, producer, _);
            //@ array_slice_deep_close_precise(1/3, s, i, producerWorkerInv, unit);
            JoinableRunnable j = ThreadingHelper.createJoinableRunnable(producer);
            //@ producer.myIndex = i;
            //@ leak producer.myIndex |-> i;
            //@ close producer.pre();
            //@ j.closeIt();
            Thread t = new Thread(j);
            t.start();
            
            producer.thread = t;
            producer.joinable = j;
            //@ close [1/3]producerWorker(unit, producer, unit);
            //@ array_slice_deep_close_precise(1/3, producers, i, producerWorker, unit);
            
            //@ close foreach_i(i + 1, nil, producerWorkerIndex);
            //@ close producerWorkerIndex(i, producer);
            //@ close foreach_i(i, cons(producer, nil), producerWorkerIndex);
            //@ foreach_i_append(0, elements, cons(producer, nil));
        }
        //@ close foreach_i(0, nil, consumerWorkerIndex);
        for (int i = 0; i < Program.consumersCount; i++)
            /*@
            invariant
                0 <= i &*& i <= consumersCount &*&
                [_]Program_consumersCount(consumersCount) &*& [_]Program_consumers(r) &*&
                [_]Program_queue(?queue) &*& [_]queue.ArrayBlockingQueue() &*& [_]atomic_space(client_inv(queue)) &*& [_]Program_receiveMaxCount(rmc) &*& 0 < rmc &*&
                [2/3]array_slice_deep(r, i, consumersCount, consumerWorkerNull, unit, _, _) &*&
                [1/3]array_slice_deep(r, 0, i, consumerWorker, unit, ?elements, _) &*& foreach_i(0, elements, consumerWorkerIndex);
            @*/
        {
            //@ array_slice_deep_split(r, i, i + 1);
            //@ array_slice_deep_open_precise(2/3, r, i);
            ConsumerThread consumer = consumers[i];
            //@ close [1/3]consumerWorkerInv(unit, consumer, _);
            //@ array_slice_deep_close_precise(1/3, r, i, consumerWorkerInv, unit);
            JoinableRunnable j = ThreadingHelper.createJoinableRunnable(consumer);
            //@ consumer.myIndex = i;
            //@ leak consumer.myIndex |-> i;
            //@ close consumer.pre();
            //@ j.closeIt();
            Thread t = new Thread(j);
            t.start();
            
            consumer.thread = t;
            consumer.joinable = j;
            //@ close [1/3]consumerWorker(unit, consumer, unit);
            //@ array_slice_deep_close_precise(1/3, consumers, i, consumerWorker, unit);
            
            //@ close foreach_i(i + 1, nil, consumerWorkerIndex);
            //@ close consumerWorkerIndex(i, consumer);
            //@ close foreach_i(i, cons(consumer, nil), consumerWorkerIndex);
            //@ foreach_i_append(0, elements, cons(consumer, nil));
        }
        
        int j;
        for (j = 0; j < Program.producersCount; j++)
            /*@
            invariant
                0 <= j &*& j <= producersCount &*&
                [_]Program_producersCount(producersCount) &*& [_]Program_producers(s) &*&
                [_]Program_queue(?queue) &*& [_]queue.ArrayBlockingQueue() &*& [_]atomic_space(client_inv(queue)) &*&
                Program_sendCount(j * smc) &*& [_]Program_sendMaxCount(smc) &*&
                [1/3]array_slice_deep(s, j, producersCount, producerWorker, unit, ?elements, _) &*& foreach_i(j, elements, producerWorkerIndex);
            @*/
        {
            ProducerThread sw = producers[j];
            ThreadingHelper.join(sw.thread, sw.joinable);
            //@ open sw.post();
            //@ open foreach_i(j, elements, producerWorkerIndex);
            //@ open producerWorkerIndex(j, sw);
            //@ int jj = sw.myIndex;
            //@ assert j == jj;
            //@ array_slice_deep_open_precise(1/3, s, j);
            //@ open producerWorkerInv(unit, sw, _);
            //@ Program.sendCount += sw.producerSendCount;
        }
        //@ assert Program.sendCount == Program.sendMaxCount * j;
        //@ assert j == producersCount;
        //@ assert Program.sendCount == Program.sendMaxCount * producersCount;
        for (j = 0; j < Program.consumersCount; j++)
            /*@
            invariant
                0 <= j &*& j <= consumersCount &*&
                [_]Program_consumersCount(consumersCount) &*& [_]Program_consumers(r) &*&
                [_]Program_queue(?queue) &*& [_]queue.ArrayBlockingQueue() &*& [_]atomic_space(client_inv(queue)) &*&
                Program_receiveCount(j * rmc) &*& [_]Program_receiveMaxCount(rmc) &*&
                [1/3]array_slice_deep(r, j, consumersCount, consumerWorker, unit, ?elements, _) &*& foreach_i(j, elements, consumerWorkerIndex);
            @*/
        {
            ConsumerThread rw = consumers[j];
            ThreadingHelper.join(rw.thread, rw.joinable);
            //@ open rw.post();
            //@ open foreach_i(j, elements, consumerWorkerIndex);
            //@ open consumerWorkerIndex(j, rw);
            //@ int jj = rw.myIndex;
            //@ assert j == jj;
            //@ array_slice_deep_open_precise(1/3, r, j);
            //@ open consumerWorkerInv(unit, rw, _);
            //@ Program.receiveCount += rw.consumerReceiveCount;
        }
        //@ assert Program.receiveCount == Program.receiveMaxCount * j;
        //@ assert j == consumersCount;
        //@ assert Program.receiveCount == Program.receiveMaxCount * consumersCount;
    }
    
}
