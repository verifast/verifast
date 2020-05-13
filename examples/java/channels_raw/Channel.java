// Work done in collaboration with Sybren Roede and Ruurd Kuiper

package channels;

import java.util.concurrent.*;
import java.util.*;

/*@

predicate_ctor channel_sema_inv(Channel channel)() =
    channel.itemList |-> ?itemList &*& itemList.List(?items) 
    &*& [1/2]channel.items_ |-> items &*&
    [1/2]channel.queueMaxSize |-> ?qms &*& length(items) <= qms;

@*/

public final class Channel {

    //@ list<Object> items_;
    List itemList;
    Semaphore sema;
    int queueMaxSize;
    
    //@ predicate Channel() = sema |-> ?sema &*& [_]sema.Semaphore(channel_sema_inv(this));
    //@ predicate ChannelState(list<Object> items, int qms) = [1/2]items_ |-> items &*& [1/2]queueMaxSize |-> qms;
    
    public Channel(int queueMaxSize)
        //@ requires 0 <= queueMaxSize;
        //@ ensures Channel() &*& ChannelState(nil, queueMaxSize);
    {
        itemList = new ArrayList();
        this.queueMaxSize = queueMaxSize;
        //@ items_ = nil;
        //@ close channel_sema_inv(this)();
        //@ one_time(channel_sema_inv(this));
        sema = new Semaphore(1);
        //@ sema.leakHandle();
        //@ close Channel();
        //@ close ChannelState(nil, queueMaxSize);
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
        //@ assert [1/2]queueMaxSize |-> ?qms;

        boolean result;
        if (itemList.size() < queueMaxSize) {
            itemList.add(msg);
            result = true;
        } else {
            result = false;
        }
        
        {
            /*@
            predicate P() =
                is_channel_sep(sep, inv, this, sepPred, unsepPred) &*&
                is_channel_unsep(unsep, inv, this, sepPred, unsepPred) &*&
                is_channel_send(send_, inv, this, unsepPred, msg, pre, post) &*&
                sepPred() &*& pre() &*&
                [1/2]items_ |-> items;
            predicate Q() =
                [1/2]items_ |-> (length(items) < qms ? append<Object>(items, cons(msg, nil)) : items) &*&
                sepPred() &*&
                post(length(items) < qms);
            
            lemma void my_ghost_op()
                requires P() &*& inv();
                ensures Q() &*& inv();
            {
                open P();
                sep();
                open ChannelState(_, _);
                if (length(items) < qms)
                {
                  items_ = append<Object>(items, cons(msg, nil));
                  close ChannelState(append<Object>(items, cons(msg, nil)), _);
                  send_(true);
                }
                else
                {
                  items_ = items;
                  close ChannelState(items, _);
                  send_(false);
                }

                unsep();
                close Q();
            }
            @*/
            //@ close P();
            //@ produce_lemma_function_pointer_chunk(my_ghost_op) : atomic_space_ghost_operation(inv, P, Q)() { call(); };
            //@ perform_atomic_space_ghost_operation();
            //@ open Q();
        }
        //@ length_append<Object>(items, cons(msg, nil));
        //@ close channel_sema_inv(this)();
        sema.release();
        //@ close [fc]Channel();
        return result;
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
                open ChannelState(_, _);
                items_ = tail(items);
                close ChannelState(tail(items), _);
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
