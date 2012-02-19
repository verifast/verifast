package channels;

import java.util.concurrent.*;
import java.util.*;

/*@

predicate_ctor channel_sema_inv(Channel channel)() =
    channel.itemList |-> ?itemList &*& itemList.List(?items) &*& [1/2]channel.items_ |-> items;

@*/

public final class Channel {

    //@ list<Object> items_;
    List itemList;
    Semaphore sema;
    
    //@ predicate Channel() = sema |-> ?sema &*& [_]sema.Semaphore(channel_sema_inv(this));
    //@ predicate ChannelState(list<Object> items) = [1/2]items_ |-> items;
    
    public Channel()
        //@ requires true;
        //@ ensures Channel() &*& ChannelState(nil);
    {
        itemList = new ArrayList();
        //@ items_ = nil;
        //@ close channel_sema_inv(this)();
        //@ one_time(channel_sema_inv(this));
        sema = new Semaphore(1);
        //@ sema.leakHandle();
        //@ close Channel();
        //@ close ChannelState(nil);
    }
    
    boolean send(String msg)
        /*@
        requires
            [?fc]Channel() &*&
            [?fa]atomic_space(?inv) &*&
            is_channel_sep(?sep, inv, this, ?sepPred, ?unsepPred) &*&
            is_channel_unsep(?unsep, inv, this, sepPred, unsepPred) &*&
            sepPred() &*&
            is_channel_send(?send_, inv, this, unsepPred, msg, ?pre, ?post) &*& pre();
        @*/
        /*@
        ensures
            [fc]Channel() &*&
            [fa]atomic_space(inv) &*&
            sepPred() &*&
            post(result);
        @*/
    {
        //@ open [fc]Channel();
        //@ sema.makeHandle();
        sema.acquire();
        //@ open channel_sema_inv(this)();
        //@ assert itemList |-> ?l &*& l.List(?items);
        itemList.add(msg);
        {
            /*@
            predicate P() =
                is_channel_sep(sep, inv, this, sepPred, unsepPred) &*&
                is_channel_unsep(unsep, inv, this, sepPred, unsepPred) &*&
                is_channel_send(send_, inv, this, unsepPred, msg, pre, post) &*&
                sepPred() &*& pre() &*&
                [1/2]items_ |-> items;
            predicate Q() =
                [1/2]items_ |-> append(items, cons(msg, nil)) &*&
                sepPred() &*&
                post(true);
            
            lemma void my_ghost_op()
                requires P() &*& inv();
                ensures Q() &*& inv();
            {
                open P();
                sep();
                open ChannelState(_);
                items_ = append(items, cons(msg, nil));
                close ChannelState(append(items, cons(msg, nil)));
                send_(true);
                unsep();
                close Q();
            }
            @*/
            //@ close P();
            //@ produce_lemma_function_pointer_chunk(my_ghost_op) : atomic_space_ghost_operation(inv, P, Q)() { call(); };
            //@ perform_atomic_space_ghost_operation();
            //@ open Q();
        }
        //@ close channel_sema_inv(this)();
        sema.release();
        //@ close [fc]Channel();
        return true;
    }
    
    String receive()
        /*@
        requires
            [?fc]Channel() &*&
            [?fa]atomic_space(?inv) &*&
            is_channel_sep(?sep, inv, this, ?sepPred, ?unsepPred) &*&
            is_channel_unsep(?unsep, inv, this, sepPred, unsepPred) &*&
            is_channel_receive(?receive_, inv, this, unsepPred, ?pre, ?post) &*&
            sepPred() &*& pre();
        @*/
        /*@
        ensures
            [fc]Channel() &*&
            [fa]atomic_space(inv) &*&
            sepPred() &*&
            post(result);
        @*/
    {
        //@ sema.makeHandle();
        sema.acquire();
        //@ open channel_sema_inv(this)();
        String result;
        if (itemList.size() == 0) {
            result = null;
        } else {
            result = (String)itemList.remove(0);
        }
        //@ list<Object> items = items_;
        {
            /*@
            predicate P() =
                is_channel_sep(sep, inv, this, sepPred, unsepPred) &*&
                is_channel_unsep(unsep, inv, this, sepPred, unsepPred) &*&
                is_channel_receive(receive_, inv, this, unsepPred, pre, post) &*&
                sepPred() &*& pre() &*&
                [1/2]items_ |-> items;
            predicate Q() =
                [1/2]items_ |-> tail(items) &*&
                sepPred() &*&
                post(items != nil ? head(items) : null);
            
            lemma void my_ghost_op()
                requires P() &*& inv();
                ensures Q() &*& inv();
            {
                open P();
                sep();
                open ChannelState(_);
                items_ = tail(items);
                close ChannelState(tail(items));
                receive_();
                unsep();
                close Q();
            }
            @*/
            //@ close P();
            //@ produce_lemma_function_pointer_chunk(my_ghost_op) : atomic_space_ghost_operation(inv, P, Q)() { call(); };
            //@ perform_atomic_space_ghost_operation();
            //@ open Q();
        }
        //@ switch (items) { case nil: case cons(i0, is0): }
        //@ close channel_sema_inv(this)();
        sema.release();
        return result;
    }
    
}
