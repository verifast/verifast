// Work done in collaboration with Sybren Roede and Ruurd Kuiper

import channels.*;
import verifast.*;

/*@

fixpoint boolean non_null(Object o) { return o != null; }

predicate_ctor client_inv(Channel c)() =
    c.ChannelState(?items, ?qms) &*& forall(items, non_null) == true &*&
    [1/2]Program_sendMaxCount(?smc) &*& 0 < smc &*&
    [1/2]Program_receiveMaxCount(?rmc) &*& 0 < rmc &*&
    [_]Program_senders(?s) &*&
    [_]Program_sendersCount(?sc) &*&
    [1/3]array_slice_deep(s, 0, sc, senderWorkerInv, unit, _, ?lstSc)  &*&
    [_]Program_receivers(?r) &*&
    [_]Program_receiversCount(?rc) &*&
    [1/3]array_slice_deep(r, 0, rc, receiverWorkerInv, unit, _, ?lstRc) &*&
    length(items) == sum(lstSc) - sum(lstRc) &*&
    sum(lstRc) <= sum(lstSc);

predicate senderWorkerInv(unit u, SenderThread sw; int senderCount) =
    [3/2]sw.senderSendCount |-> senderCount;

predicate receiverWorkerInv(unit u, ReceiverThread rw; int receiverCount) =
    [3/2]rw.receiverReceiveCount |-> receiverCount;

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

predicate_ctor my_unsep_pred(Channel c)(list<Object> items, int qms) =
    forall(items, non_null) == true &*&
    [1/2]Program_sendMaxCount(?smc) &*&  0 < smc &*&
    [1/2]Program_receiveMaxCount(?rmc) &*& 0 < rmc &*&
    [_]Program_senders(?s) &*&
    [_]Program_sendersCount(?sc) &*&
    [1/3]array_slice_deep(s, 0, sc, senderWorkerInv, unit, _, ?lstSc)  &*&
    [_]Program_receivers(?r) &*&
    [_]Program_receiversCount(?rc) &*&
    [1/3]array_slice_deep(r, 0, rc, receiverWorkerInv, unit, _, ?lstRc) &*&
    length(items) == sum(lstSc) - sum(lstRc) &*&
    sum(lstRc) <= sum(lstSc);

lemma void my_sep()
    requires exists<Channel>(?c) &*& my_sep_pred() &*& client_inv(c)();
    ensures c.ChannelState(?items, ?qms) &*& my_unsep_pred(c)(items, qms);
{
    open client_inv(c)();
    assert c.ChannelState(?items, ?qms);
    close my_unsep_pred(c)(items, qms);
}

lemma void my_unsep()
    requires exists<Channel>(?c) &*& my_unsep_pred(c)(?items, ?qms) &*& c.ChannelState(items, qms);
    ensures my_sep_pred() &*& client_inv(c)();
{
    open my_unsep_pred(c)(_, _);
    close client_inv(c)();
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

predicate senderWorker(unit u, SenderThread SenderWorker; unit u2) =
    [3]SenderWorker.thread |-> ?t &*&  [3]SenderWorker.joinable |-> ?j &*&
    [3]t.Thread(j, true) &*& [3]j.JoinableRunnable(SenderWorker, true) &*& SenderWorker.getClass() == SenderThread.class &*&
    u2 == unit;

predicate senderWorkerNull(unit u, SenderThread SenderWorker; unit u2) =
    [3/2]SenderWorker.thread |-> _ &*&  [3/2]SenderWorker.joinable |-> _ &*&
    [3/2]SenderWorker.myIndex |-> _ &*&
    SenderWorker.getClass() == SenderThread.class &*& [3/4]SenderWorker.senderSendCount |-> 0 &*&
    u2 == unit;

predicate senderWorkerIndex(int i, SenderThread t) =
    [_]t.myIndex |-> i;

@*/

public class SenderThread implements Runnable {
    
    //@ int senderSendCount;
    //@ int myIndex;
    Thread thread;
    JoinableRunnable joinable;
    
    /*@
    
    predicate pre()  =
        [_]Program_channel(?c) &*& [_]c.Channel() &*& [_]atomic_space(client_inv(c)) &*&
        [_]Program_sendMaxCount(?smc) &*& 0 < smc &*&
        [_]Program_senders(?s) &*& [_]this.myIndex |-> ?myIndex &*&
        [_]Program_sendersCount(?sc) &*& myIndex < sc  &*&
        [1/3]array_slice_deep(s, myIndex, myIndex + 1, senderWorkerInv, unit, cons(this, nil), cons(0, nil));
    
    predicate post() =
        [_]Program_channel(?c) &*& [_]c.Channel() &*& [_]atomic_space(client_inv(c)) &*&
        [_]Program_sendMaxCount(?smc) &*&
        [_]Program_senders(?s) &*& [_]this.myIndex |-> ?myIndex &*&
        [_]Program_sendersCount(?sc) &*& myIndex < sc  &*&
        [1/3]array_slice_deep(s, myIndex, myIndex + 1, senderWorkerInv, unit, cons(this, nil), cons(smc, nil));
    
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
                [_]Program_channel(?c) &*& [_]c.Channel() &*& [_]atomic_space(client_inv(c)) &*&
                [_]Program_sendMaxCount(?smc) &*& i <= smc &*&
                [_]Program_senders(?s) &*& [_]this.myIndex |-> ?myIndex &*&
                [_]Program_sendersCount(?sc) &*& myIndex < sc &*&
                [1/3]array_slice_deep(s, myIndex, myIndex + 1, senderWorkerInv, unit, cons(this, nil), cons(i, nil));
            @*/
        {
            for (;;)
                /*@
                invariant
                    [_]Program_channel(c) &*& [_]c.Channel() &*& [_]atomic_space(client_inv(c)) &*&
                    [_]Program_sendMaxCount(smc) &*& i < smc &*&
                    [_]Program_senders(s) &*& [_]this.myIndex |-> myIndex &*&
                    [_]Program_sendersCount(sc) &*& myIndex < sc &*&
                    [1/3]array_slice_deep(s, myIndex, myIndex + 1, senderWorkerInv, unit, cons(this, nil), cons(i, nil));
                @*/
            {
                
                /*@
                predicate P() =
                    [_]Program_sendMaxCount(smc) &*&
                    [_]Program_senders(s) &*& [_]this.myIndex |-> myIndex &*&
                    [_]Program_sendersCount(sc) &*& myIndex < sc &*&
                    [1/3]array_slice_deep(s, myIndex, myIndex + 1, senderWorkerInv, unit, cons(this, nil), cons(i, nil));
                predicate Q(boolean r) =
                    [_]Program_sendMaxCount(smc) &*&
                    [_]Program_senders(s) &*& [_]this.myIndex |-> myIndex &*&
                    [_]Program_sendersCount(sc) &*& myIndex < sc &*&
                    [1/3]array_slice_deep(s, myIndex, myIndex + 1, senderWorkerInv, unit, cons(this, nil), (r ? cons(i+1, nil) : cons(i, nil)));
                
                lemma void my_send(boolean r)
                    requires i < smc &*& P() &*& my_unsep_pred(c)(?items, ?qms);
                    ensures Q(r) &*& my_unsep_pred(c)(r ? append(items, cons(m, nil)) : items, qms);
                {
                    open P();
                    open my_unsep_pred(c)(items, qms);
                    SenderThread[] senders = Program.senders;
                    int sendersCount = Program.sendersCount;
                    int k = myIndex;
                    assert [1/3]array_slice_deep(senders, 0, sendersCount, senderWorkerInv, unit, _, ?oldSenderCounts);
                    array_slice_deep_split(Program.senders, 0, myIndex);
                    array_slice_deep_split_precise(1/3, Program.senders, myIndex, Program.sendersCount, senderWorkerInv, unit, myIndex + 1);
                    array_slice_deep_open_precise(2/3, Program.senders, myIndex);
                    int myOldSendCount = senderSendCount;
                    if (r) {
                        senderSendCount++;
                    }
                    int myNewSendCount = senderSendCount;
                    array_slice_deep_close(Program.senders, myIndex, senderWorkerInv, unit);
                    array_slice_deep_join_precise(1/3, Program.senders, myIndex, myIndex + 1, senderWorkerInv, unit, Program.sendersCount);
                    array_slice_deep_join_precise(1/3, Program.senders, 0, myIndex, senderWorkerInv, unit, Program.sendersCount);
                    
                    forall_append(items, cons(m, nil), non_null);
                    length_append(items, cons(m, nil));
                    assert [1/3]array_slice_deep(senders, 0, sendersCount, senderWorkerInv, unit, _, ?newSenderCounts);
                    assert newSenderCounts == append(take(k, oldSenderCounts), cons(myNewSendCount, drop(1, drop(k, oldSenderCounts))));
                    assert length(oldSenderCounts) == sendersCount;
                    assert 0 <= 1 &*& 0 <= k &*& 1 + k <= length(oldSenderCounts);
                    drop_drop(1, k, oldSenderCounts);
                    assert newSenderCounts == append(take(k, oldSenderCounts), cons(myNewSendCount, drop(k + 1, oldSenderCounts)));
                    sum_take_cons_drop(k, oldSenderCounts, myNewSendCount);
                    assert sum(newSenderCounts) == sum(oldSenderCounts) + myNewSendCount - myOldSendCount;
                    close my_unsep_pred(c)(r ? append(items, cons(m, nil)) : items, qms);
                    close Q(r);
                }
                @*/
                //@ produce_lemma_function_pointer_chunk(my_sep) : channel_sep(client_inv(c), c, my_sep_pred, my_unsep_pred(c))() { close exists(c); call(); };
                //@ produce_lemma_function_pointer_chunk(my_unsep) : channel_unsep(client_inv(c), c, my_sep_pred, my_unsep_pred(c))() { close exists(c); call(); };
                //@ close my_sep_pred();
                //@ produce_lemma_function_pointer_chunk(my_send) : channel_send(client_inv(c), c, my_unsep_pred(c), m, P, Q)(r) { call(); };
                //@ close P();
                boolean success = Program.channel.send(m);
                //@ open Q(success);
                if (success) break;
            }
        }
        //@ assert i == Program.sendMaxCount;
        //@ close post();
    }
}

/*@

predicate receiverWorker(unit u, ReceiverThread ReceiverWorker; unit u2) =
    [3]ReceiverWorker.thread |-> ?t &*& [3]ReceiverWorker.joinable |-> ?j &*&
    [3]t.Thread(j, true) &*& [3]j.JoinableRunnable(ReceiverWorker, true) &*& ReceiverWorker.getClass() == ReceiverThread.class &*&
    u2 == unit;

predicate receiverWorkerNull(unit u, ReceiverThread ReceiverWorker; unit u2) =
    [3/2]ReceiverWorker.thread |-> _ &*&  [3/2]ReceiverWorker.joinable |-> _ &*&
    [3/2]ReceiverWorker.myIndex |-> _ &*&
    ReceiverWorker.getClass() == ReceiverThread.class &*& [3/4]ReceiverWorker.receiverReceiveCount |-> 0 &*&
    u2 == unit;

predicate receiverWorkerIndex(int i, ReceiverThread t) =
    [_]t.myIndex |-> i;

@*/

class ReceiverThread implements Runnable {
    //@ int receiverReceiveCount;
    //@ int myIndex;
    Thread thread;
    JoinableRunnable joinable;
    
    /*@
    
    predicate pre() =
        [_]Program_channel(?c) &*& [_]c.Channel() &*& [_]atomic_space(client_inv(c)) &*&
        [_]Program_receiveMaxCount(?rmc) &*& 0 < rmc &*&
        [_]Program_receivers(?s) &*& [_]this.myIndex |-> ?myIndex &*&
        [_]Program_receiversCount(?rc) &*& myIndex < rc  &*&
        [1/3]array_slice_deep(s, myIndex, myIndex + 1, receiverWorkerInv, unit, cons(this, nil), cons(0, nil));
    
    predicate post() =
        [_]Program_channel(?c) &*& [_]c.Channel() &*& [_]atomic_space(client_inv(c)) &*&
        [_]Program_receiveMaxCount(?rmc) &*&
        [_]Program_receivers(?s) &*& [_]this.myIndex |-> ?myIndex &*&
        [_]Program_receiversCount(?rc) &*& myIndex < rc  &*&
        [1/3]array_slice_deep(s, myIndex, myIndex + 1, receiverWorkerInv, unit, cons(this, nil), cons(rmc, nil));
    
    @*/
    
    public void run()
        //@ requires pre();
        //@ ensures post();
    {
        int i;
        for (i=0; i < Program.receiveMaxCount; i++)
            /*@
            invariant
                [_]Program_channel(?c) &*& [_]c.Channel() &*& [_]atomic_space(client_inv(c)) &*&
                [_]Program_receiveMaxCount(?rmc) &*& i <= rmc &*&
                [_]Program_receivers(?r) &*& [_]this.myIndex |-> ?myIndex &*&
                [_]Program_receiversCount(?rc) &*& myIndex < rc &*&
                [1/3]array_slice_deep(r, myIndex, myIndex + 1, receiverWorkerInv, unit, cons(this, nil), cons(i, nil));
            @*/
        {
            for (;;)
                /*@
                invariant
                    [_]Program_channel(c) &*& [_]c.Channel() &*& [_]atomic_space(client_inv(c)) &*&
                    [_]Program_receiveMaxCount(rmc) &*& i < rmc &*&
                    [_]Program_receivers(r) &*& [_]this.myIndex |-> myIndex &*&
                    [_]Program_receiversCount(rc) &*& myIndex < rc &*&
                    [1/3]array_slice_deep(r, myIndex, myIndex + 1, receiverWorkerInv, unit, cons(this, nil), cons(i, nil));
                @*/
            {
                /*@
                predicate P() =  
                    [_]Program_receiveMaxCount(rmc) &*&
                    [_]Program_receivers(r) &*& [_]this.myIndex |-> myIndex &*&
                    [_]Program_receiversCount(rc) &*& myIndex < rc &*&
                    [1/3]array_slice_deep(r, myIndex, myIndex + 1, receiverWorkerInv, unit, cons(this, nil), cons(i, nil));
                predicate Q(Object result) = 
                    [_]Program_receiveMaxCount(rmc) &*& 
                    [_]Program_receivers(r) &*& [_]this.myIndex |-> myIndex &*& 
                    [_]Program_receiversCount(rc) &*& myIndex < rc &*&
                    [1/3]array_slice_deep(r, myIndex, myIndex + 1, receiverWorkerInv, unit, cons(this, nil), (result != null ? cons(i + 1, nil) : cons(i , nil)));
                
                lemma void my_channel_receive()
                    requires i < rmc &*& P() &*& my_unsep_pred(c)(?items, ?qms);
                    ensures Q(items != nil ? head(items) : null) &*& my_unsep_pred(c)(tail(items), qms);
                {
                    open P();
                    open my_unsep_pred(c)(items, qms);
                    ReceiverThread[] receivers = Program.receivers;
                    int receiversCount = Program.receiversCount;
                    int k = myIndex;
                    assert [1/3]array_slice_deep(receivers, 0, receiversCount, receiverWorkerInv, unit, _, ?oldReceiverCounts);
                    array_slice_deep_split(Program.receivers, 0, myIndex);
                    array_slice_deep_split_precise(1/3, Program.receivers, myIndex, Program.receiversCount, receiverWorkerInv, unit, myIndex + 1);
                    array_slice_deep_open_precise(2/3, Program.receivers, myIndex);
                    int myOldReceiveCount = receiverReceiveCount;
                    switch (items) {
                    case nil:
                    case cons(head, tail):
                        receiverReceiveCount++;
                    }
                    int myNewReceiverCount = receiverReceiveCount;
                    array_slice_deep_close(Program.receivers, myIndex, receiverWorkerInv, unit);
                    array_slice_deep_join_precise(1/3, Program.receivers, myIndex, myIndex + 1, receiverWorkerInv, unit, Program.receiversCount);
                    array_slice_deep_join_precise(1/3, Program.receivers, 0, myIndex, receiverWorkerInv, unit, Program.receiversCount);
                    
                    assert [1/3]array_slice_deep(receivers, 0, receiversCount, receiverWorkerInv, unit, _, ?newReceiverCounts);
                    assert newReceiverCounts == append(take(k, oldReceiverCounts), cons(myNewReceiverCount, drop(1, drop(k, oldReceiverCounts))));
                    assert length(oldReceiverCounts) == receiversCount;
                    assert 0 <= 1 &*& 0 <= k &*& 1 + k <= length(oldReceiverCounts);
                    drop_drop(1, k, oldReceiverCounts);
                    assert newReceiverCounts == append(take(k, oldReceiverCounts), cons(myNewReceiverCount, drop(k + 1, oldReceiverCounts)));
                    sum_take_cons_drop(k, oldReceiverCounts, myNewReceiverCount);
                    assert sum(newReceiverCounts) == sum(oldReceiverCounts) + myNewReceiverCount - myOldReceiveCount;
                    
                    switch (items) {
                    case nil:
                        close my_unsep_pred(c)(items, qms);
                        close Q(null);
                    case cons(head, tail):
                        close my_unsep_pred(c)(tail, qms);
                        close Q(head);
                    }
                }
                @*/
                //@ produce_lemma_function_pointer_chunk(my_sep) : channel_sep(client_inv(c), c, my_sep_pred, my_unsep_pred(c))() { close exists(c); call(); };
                //@ produce_lemma_function_pointer_chunk(my_unsep) : channel_unsep(client_inv(c), c, my_sep_pred, my_unsep_pred(c))() { close exists(c); call(); };
                //@ close my_sep_pred();
                //@ produce_lemma_function_pointer_chunk(my_channel_receive) : channel_receive(client_inv(c), c, my_unsep_pred(c), P, Q)() { call(); };
                //@ close P();
                String m = Program.channel.receive();
                //@ open Q(m);
                if (m != null) break;
            }
        }
        //@ close post();
    }
}

public class Program {
    
    //@ static int sendCount;
    //@ static int receiveCount;
    
    public static int sendMaxCount;
    public static int receiveMaxCount;
    public static Channel channel;
    public static int sendersCount;
    public static int receiversCount;
    public static SenderThread[] senders;
    public static ReceiverThread[] receivers;
    
    public static void main(String[] args)
        //@ requires class_init_token(Program.class);
        //@ ensures true;
    {
        //@ init_class();
        Program.sendersCount = 1000;
        Program.receiversCount = 1000;
        Program.sendMaxCount = 2000;
        Program.receiveMaxCount = 2000;
        Program.work();
        //@assert Program.sendCount == 2000000;
        //@assert Program.receiveCount == 2000000;
    }
    
    public static void work()
        /*@
        requires
            Program_channel(?channel) &*&
            Program_senders(_) &*& Program_receivers(_) &*&
            [_]Program_sendersCount(?sendersCount) &*& [_]Program_receiversCount(?receiversCount) &*&
            0 < sendersCount &*& 0 < receiversCount &*&
            Program_sendCount(?psc) &*& Program_receiveCount(?prc) &*& psc==0 &*& prc==0 &*&
            Program_sendMaxCount(?smc) &*& 0 < smc  &*& Program_receiveMaxCount(?rmc) &*& 0 < rmc;
        @*/
        //@ ensures Program_sendCount(smc * sendersCount) &*& Program_receiveCount(rmc * receiversCount);
     {
        Program.senders = new SenderThread[Program.sendersCount];
        //@ SenderThread[] s = Program.senders;
        //@ leak Program_senders(s);
        //@ array_slice_deep_empty_close(s, 0, senderWorker, unit);
        for (int i = 0; i < Program.sendersCount; i++)
            /*@
            invariant
                0 <= i &*& i <= sendersCount &*&
                [_]Program_senders(s) &*& [_]Program_sendersCount(sendersCount) &*&
                [1/3]Program_sendMaxCount(smc) &*& 0 < smc &*&
                array_slice(s, i, sendersCount, ?elems) &*& all_eq(elems, null) == true &*&
                [1/3]array_slice_deep(s, 0, i, senderWorkerInv, unit, _, ?v) &*& all_eq(v, 0) == true &*&
                [2/3]array_slice_deep(s, 0, i, senderWorkerNull, unit, _, _);
            @*/
        {
            Program.senders[i] = new SenderThread();
            //@ Program.senders[i].myIndex = i;
            //@ array_slice_split(senders, i, i + 1);
            //@ close [2/3]senderWorkerNull(unit, senders[i], unit);
            //@ close [1/3]senderWorkerInv(unit, senders[i], _);
            //@ array_slice_deep_close_precise(2/3, senders, i, senderWorkerNull, unit);
            //@ array_slice_deep_close_precise(1/3, senders, i, senderWorkerInv, unit);
            
        }
        
        Program.receivers = new ReceiverThread[Program.receiversCount];
        //@ ReceiverThread[] r = Program.receivers;
        //@ leak Program_receivers(r);
        //@ array_slice_deep_empty_close(r, 0, receiverWorker, unit);
        for (int i = 0; i < Program.receiversCount; i++)
            /*@
            invariant
                0 <= i &*& i <= receiversCount &*&
                [_]Program_receivers(r) &*& [_]Program_receiversCount(receiversCount) &*&
                [1/3]Program_receiveMaxCount(rmc) &*& 0 < rmc &*&
                array_slice(r, i, receiversCount, ?elems) &*& all_eq(elems, null) == true &*&
                [1/3]array_slice_deep(r, 0, i, receiverWorkerInv, unit, _, ?v) &*& all_eq(v, 0) == true &*&
                [2/3]array_slice_deep(r, 0, i, receiverWorkerNull, unit, _, _);
            @*/
        {
            receivers[i] = new ReceiverThread();
            //@ Program.receivers[i].myIndex = i;
            //@ array_slice_split(receivers, i, i + 1);
            //@ close [2/3]receiverWorkerNull(unit, receivers[i], unit);
            //@ close [1/3]receiverWorkerInv(unit, receivers[i], _);
            //@ array_slice_deep_close_precise(2/3, receivers, i, receiverWorkerNull, unit);
            //@ array_slice_deep_close_precise(1/3, receivers, i, receiverWorkerInv, unit);
        }
        Program.channel = new Channel(2);
        
        //@ close client_inv(Program.channel)();
        //@ create_atomic_space(client_inv(Program.channel));
        //@ close foreach_i(0, nil, senderWorkerIndex);
        
        for (int i = 0; i < Program.sendersCount; i++)
            /*@
            invariant
                0 <= i &*& i <= sendersCount &*&
                [_]Program_sendersCount(sendersCount) &*& [_]Program_senders(s) &*&
                [_]Program_channel(?c) &*& [_]c.Channel() &*& [_]atomic_space(client_inv(c)) &*& [_]Program_sendMaxCount(smc) &*& 0 < smc &*&
                [2/3]array_slice_deep(s, i, sendersCount, senderWorkerNull, unit, _, _) &*&
                [1/3]array_slice_deep(s, 0, i, senderWorker, unit, ?elements, _) &*& foreach_i(0, elements, senderWorkerIndex);
            @*/
        {
            //@ array_slice_deep_split(s, i, i + 1);
            //@ array_slice_deep_open_precise(2/3, s, i);
            SenderThread sender = senders[i];
            //@ close [1/3]senderWorkerInv(unit, sender, _);
            //@ array_slice_deep_close_precise(1/3, s, i, senderWorkerInv, unit);
            JoinableRunnable j = ThreadingHelper.createJoinableRunnable(sender);
            //@ sender.myIndex = i;
            //@ leak sender.myIndex |-> i;
            //@ close sender.pre();
            //@ j.closeIt();
            Thread t = new Thread(j);
            t.start();
            
            sender.thread = t;
            sender.joinable = j;
            //@ close [1/3]senderWorker(unit, sender, unit);
            //@ array_slice_deep_close_precise(1/3, senders, i, senderWorker, unit);
            
            //@ close foreach_i(i + 1, nil, senderWorkerIndex);
            //@ close senderWorkerIndex(i, sender);
            //@ close foreach_i(i, cons(sender, nil), senderWorkerIndex);
            //@ foreach_i_append(0, elements, cons(sender, nil));
        }
        //@ close foreach_i(0, nil, receiverWorkerIndex);
        for (int i = 0; i < Program.receiversCount; i++)
            /*@
            invariant
                0 <= i &*& i <= receiversCount &*&
                [_]Program_receiversCount(receiversCount) &*& [_]Program_receivers(r) &*&
                [_]Program_channel(?c) &*& [_]c.Channel() &*& [_]atomic_space(client_inv(c)) &*& [_]Program_receiveMaxCount(rmc) &*& 0 < rmc &*&
                [2/3]array_slice_deep(r, i, receiversCount, receiverWorkerNull, unit, _, _) &*&
                [1/3]array_slice_deep(r, 0, i, receiverWorker, unit, ?elements, _) &*& foreach_i(0, elements, receiverWorkerIndex);
            @*/
        {
            //@ array_slice_deep_split(r, i, i + 1);
            //@ array_slice_deep_open_precise(2/3, r, i);
            ReceiverThread receiver = receivers[i];
            //@ close [1/3]receiverWorkerInv(unit, receiver, _);
            //@ array_slice_deep_close_precise(1/3, r, i, receiverWorkerInv, unit);
            JoinableRunnable j = ThreadingHelper.createJoinableRunnable(receiver);
            //@ receiver.myIndex = i;
            //@ leak receiver.myIndex |-> i;
            //@ close receiver.pre();
            //@ j.closeIt();
            Thread t = new Thread(j);
            t.start();
            
            receiver.thread = t;
            receiver.joinable = j;
            //@ close [1/3]receiverWorker(unit, receiver, unit);
            //@ array_slice_deep_close_precise(1/3, receivers, i, receiverWorker, unit);
            
            //@ close foreach_i(i + 1, nil, receiverWorkerIndex);
            //@ close receiverWorkerIndex(i, receiver);
            //@ close foreach_i(i, cons(receiver, nil), receiverWorkerIndex);
            //@ foreach_i_append(0, elements, cons(receiver, nil));
        }
        
        int j;
        for (j = 0; j < Program.sendersCount; j++)
            /*@
            invariant
                0 <= j &*& j <= sendersCount &*&
                [_]Program_sendersCount(sendersCount) &*& [_]Program_senders(s) &*&
                [_]Program_channel(?c) &*& [_]c.Channel() &*& [_]atomic_space(client_inv(c)) &*&
                Program_sendCount(j * smc) &*& [_]Program_sendMaxCount(smc) &*&
                [1/3]array_slice_deep(s, j, sendersCount, senderWorker, unit, ?elements, _) &*& foreach_i(j, elements, senderWorkerIndex);
            @*/
        {
            SenderThread sw = senders[j];
            ThreadingHelper.join(sw.thread, sw.joinable);
            //@ open sw.post();
            //@ open foreach_i(j, elements, senderWorkerIndex);
            //@ open senderWorkerIndex(j, sw);
            //@ int jj = sw.myIndex;
            //@ assert j == jj;
            //@ array_slice_deep_open_precise(1/3, s, j);
            //@ open senderWorkerInv(unit, sw, _);
            //@ Program.sendCount += sw.senderSendCount;
        }
        //@ assert Program.sendCount == Program.sendMaxCount * j;
        //@ assert j == sendersCount;
        //@ assert Program.sendCount == Program.sendMaxCount * sendersCount;
        for (j = 0; j < Program.receiversCount; j++)
            /*@
            invariant
                0 <= j &*& j <= receiversCount &*&
                [_]Program_receiversCount(receiversCount) &*& [_]Program_receivers(r) &*&
                [_]Program_channel(?c) &*& [_]c.Channel() &*& [_]atomic_space(client_inv(c)) &*&
                Program_receiveCount(j * rmc) &*& [_]Program_receiveMaxCount(rmc) &*&
                [1/3]array_slice_deep(r, j, receiversCount, receiverWorker, unit, ?elements, _) &*& foreach_i(j, elements, receiverWorkerIndex);
            @*/
        {
            ReceiverThread rw = receivers[j];
            ThreadingHelper.join(rw.thread, rw.joinable);
            //@ open rw.post();
            //@ open foreach_i(j, elements, receiverWorkerIndex);
            //@ open receiverWorkerIndex(j, rw);
            //@ int jj = rw.myIndex;
            //@ assert j == jj;
            //@ array_slice_deep_open_precise(1/3, r, j);
            //@ open receiverWorkerInv(unit, rw, _);
            //@ Program.receiveCount += rw.receiverReceiveCount;
        }
        //@ assert Program.receiveCount == Program.receiveMaxCount * j;
        //@ assert j == receiversCount;
        //@ assert Program.receiveCount == Program.receiveMaxCount * receiversCount;
    }
    
}
