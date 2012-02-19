import channels.*;

/*@

fixpoint boolean non_null(Object o) { return o != null; }

predicate_ctor client_inv(Channel c)() =
    c.ChannelState(?items) &*& forall(items, non_null) == true &*&
    [1/2]Program_sendCount(?sc) &*&
    0 <= sc &*& sc <= 10 &*&
    [1/2]Program_receiveCount(?rc) &*&
    0 <= rc &*& rc <= 10 &*&
    length(items) == sc - rc;

predicate my_sep_pred() = true;

predicate_ctor my_unsep_pred(Channel c)(list<Object> items) =
    forall(items, non_null) == true &*&
    [1/2]Program_sendCount(?sc) &*&
    0 <= sc &*& sc <= 10 &*&
    [1/2]Program_receiveCount(?rc) &*&
    0 <= rc &*& rc <= 10 &*&
    length(items) == sc - rc;

lemma void my_sep()
    requires exists<Channel>(?c) &*& my_sep_pred() &*& client_inv(c)();
    ensures c.ChannelState(?items) &*& my_unsep_pred(c)(items);
{
    open client_inv(c)();
    assert c.ChannelState(?items);
    close my_unsep_pred(c)(items);
}

lemma void my_unsep()
    requires exists<Channel>(?c) &*& my_unsep_pred(c)(?items) &*& c.ChannelState(items);
    ensures my_sep_pred() &*& client_inv(c)();
{
    open my_unsep_pred(c)(_);
    close client_inv(c)();
    close my_sep_pred();
}

@*/

class SenderThread implements Runnable {

    Channel c;
    
    //@ predicate pre() = this.c |-> ?c &*& [_]c.Channel() &*& [1/2]atomic_space(client_inv(c)) &*& [1/2]Program_sendCount(0);
    //@ predicate post() = true;
    
    SenderThread(Channel c)
        //@ requires [_]c.Channel() &*& [1/2]atomic_space(client_inv(c)) &*& [1/2]Program_sendCount(0);
        //@ ensures pre();
    {
        this.c = c;
    }
    
    public void run()
        //@ requires pre();
        //@ ensures post();
    {
        String m = "Hello";
        for (int i = 0; i < 10; i++)
            //@ invariant this.c |-> ?c &*& [_]c.Channel() &*& [1/2]atomic_space(client_inv(c)) &*& [1/2]Program_sendCount(i);
        {
            for (;;)
                //@ invariant this.c |-> c &*& [_]c.Channel() &*& [1/2]atomic_space(client_inv(c)) &*& [1/2]Program_sendCount(i);
            {
                /*@
                predicate P() = [1/2]Program_sendCount(i);
                
                predicate Q(boolean r) = [1/2]Program_sendCount(r ? i + 1 : i);
                
                lemma void my_send(boolean r)
                    requires i < 10 &*& P() &*& my_unsep_pred(c)(?items);
                    ensures Q(r) &*& my_unsep_pred(c)(r ? append(items, cons(m, nil)) : items);
                {
                    open P();
                    open my_unsep_pred(c)(items);
                    if (r) Program.sendCount++;
                    close Q(r);
                    forall_append(items, cons(m, nil), non_null);
                    close my_unsep_pred(c)(r ? append(items, cons(m, nil)) : items);
                }
                @*/
                //@ produce_lemma_function_pointer_chunk(my_sep) : channel_sep(client_inv(c), c, my_sep_pred, my_unsep_pred(c))() { close exists(c); call(); };
                //@ produce_lemma_function_pointer_chunk(my_unsep) : channel_unsep(client_inv(c), c, my_sep_pred, my_unsep_pred(c))() { close exists(c); call(); };
                //@ close my_sep_pred();
                //@ produce_lemma_function_pointer_chunk(my_send) : channel_send(client_inv(c), c, my_unsep_pred(c), m, P, Q)(r) { call(); };
                //@ close P();
                boolean success = this.c.send(m);
                //@ open Q(success);
                if (success) break;
            }
        }
        //@ close post();
    }

}

class ReceiverThread implements Runnable {

    Channel c;
    
    //@ predicate pre() = this.c |-> ?c &*& [_]c.Channel() &*& [1/2]atomic_space(client_inv(c)) &*& [1/2]Program_receiveCount(0);
    //@ predicate post() = true;
    
    ReceiverThread(Channel c)
        //@ requires [_]c.Channel() &*& [1/2]atomic_space(client_inv(c)) &*& [1/2]Program_receiveCount(0);
        //@ ensures pre();
    {
        this.c = c;
    }
    
    public void run()
        //@ requires pre();
        //@ ensures post();
    {
        for (int i = 0; i < 10; i++)
            //@ invariant this.c |-> ?c &*& [_]c.Channel() &*& [1/2]atomic_space(client_inv(c)) &*& [1/2]Program_receiveCount(i);
        {
            for (;;)
                //@ invariant this.c |-> c &*& [_]c.Channel() &*& [1/2]atomic_space(client_inv(c)) &*& [1/2]Program_receiveCount(i);
            {
                /*@
                predicate P() = [1/2]Program_receiveCount(i);
                
                predicate Q(Object r) = [1/2]Program_receiveCount(r == null ? i : i + 1);
                
                lemma void my_channel_receive()
                    requires i < 10 &*& P() &*& my_unsep_pred(c)(?items);
                    ensures Q(items != nil ? head(items) : null) &*& my_unsep_pred(c)(tail(items));
                {
                    open P();
                    open my_unsep_pred(c)(items);
                    switch (items) {
                       case nil:
                           close Q(null);
                           close my_unsep_pred(c)(items);
                       case cons(head, tail):
                           Program.receiveCount++;
                           close Q(head);
                           close my_unsep_pred(c)(tail);
                    }
                }
                @*/
                //@ produce_lemma_function_pointer_chunk(my_sep) : channel_sep(client_inv(c), c, my_sep_pred, my_unsep_pred(c))() { close exists(c); call(); };
                //@ produce_lemma_function_pointer_chunk(my_unsep) : channel_unsep(client_inv(c), c, my_sep_pred, my_unsep_pred(c))() { close exists(c); call(); };
                //@ close my_sep_pred();
                //@ produce_lemma_function_pointer_chunk(my_channel_receive) : channel_receive(client_inv(c), c, my_unsep_pred(c), P, Q)() { call(); };
                //@ close P();
                String m = this.c.receive();
                //@ open Q(m);
                if (m != null) break;
            }
        }
        //@ close post();
    }

}

class Program {
    
    //@ static int sendCount;
    //@ static int receiveCount;
    
    public static void main(String[] args)
        //@ requires class_init_token(Program.class);
        //@ ensures true;
    {
        //@ init_class();
        Channel c = new Channel();
        //@ close client_inv(c)();
        //@ create_atomic_space(client_inv(c));
        //@ leak c.Channel();
        new Thread(new SenderThread(c)).start();
        new Thread(new ReceiverThread(c)).start();
    }
    
}