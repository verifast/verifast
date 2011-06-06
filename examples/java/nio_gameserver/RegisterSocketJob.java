package gameserver;

import java.nio.channels.*;
import java.util.*;

/*@
predicate registersocketjob(RegisterSocketJob job) = 
    job.channel |-> ?channel &*& channel != null &*& channel(channel, 0)
    &*& job.ops |-> ?ops &*& ops != 0 
    &*& job.command |-> ?command &*& command != null &*& socket_command(command.getClass())(command, channel) 
    &*& is_socket_command_to_runnable(?lemmaPointer, command.getClass());

lemma void contains_list_helper(SelectableChannel channel, pair<SelectableChannel, Runnable> val, list<pair<SelectableChannel, Runnable> > vals, list<pair<SelectionKey, SelectableChannel> > keys)
requires mem(channel, snd_list(keys)) == false &*& keys_equals_map(keys, vals) == true &*& mem(val, vals) == true;
ensures fst(val) != channel;
{
	switch (vals) {
             case nil:
             case cons(val0, vals0):
        		if(val0 == val) {
        		}
        		else {
        			tails_equal(keys, vals);
        			contains_list_helper(channel, val, vals0, tail(keys));
        		}
        }
}

lemma void contains_list(SelectableChannel channel, list<pair<SelectableChannel, Runnable> > vals, list<pair<SelectionKey, SelectableChannel> > keys)
requires channel(channel, ?r) &*& foreach(snd_list(keys), @channel_wrapper) &*& keys_equals_map(keys, vals) == true;
ensures contains_key(channel, vals) == false &*& channel(channel, r) &*& foreach(snd_list(keys), @channel_wrapper);
{               
      switch (vals) {
             case nil:
             case cons(val0, vals0):
                    	if (mem(channel, snd_list(keys)) == true) {
                           	foreach_remove(channel, snd_list(keys));
                           	open channel_wrapper(channel);
				channel_unique(channel);
				close channel_wrapper(channel);
				foreach_unremove(channel, snd_list(keys));  
			} 
			else {
				contains_list_helper(channel, val0, vals, keys);
			}
			
			tails_equal(keys, vals);
			
			foreach_remove_nth(0, snd_list(keys));
			contains_list(channel, vals0, tail(keys));   
			foreach_unremove_nth(0, snd_list(keys));                                                                                                     
      }
}

lemma void convert_appends(SelectionKey key, SelectableChannel channel, list<pair<SelectionKey, SelectableChannel> > keys)
 requires true;
 ensures fst_list(append(keys, cons(pair(key, channel), nil))) == append(fst_list(keys), cons(key, nil))
     &*& snd_list(append(keys, cons(pair(key, channel), nil))) == append(snd_list(keys), cons(channel, nil));
{
    switch(keys) {
        case nil:
        case cons(key0, keys0):
            convert_appends(key, channel, keys0);
    }
}

lemma void maintain_distinct_append_helper<t, u>(t key, u value, pair<t, u> val, list<pair<t, u> > vals)
requires mem(fst(val), fst_list(vals)) == false &*& fst(val) != key
    &*& mem(snd(val), snd_list(vals)) == false &*& snd(val) != value;
ensures mem(fst(val), fst_list(append(vals, cons(pair(key, value), nil)))) == false
    &*& mem(snd(val), snd_list(append(vals, cons(pair(key, value), nil)))) == false;
{
    switch (vals) {
        case nil:
        case cons(val0, vals0):
            maintain_distinct_append_helper(key, value, val, vals0);
    }
}

lemma void maintain_distinct_append<t, u>(t key, u value, list<pair<t, u> > vals)
 requires distinct(fst_list(vals)) == true &*& distinct(snd_list(vals)) == true 
         &*& mem(key, fst_list(vals)) == false &*& mem(value, snd_list(vals)) == false;
 ensures distinct(fst_list(append(vals, cons(pair(key, value), nil)))) == true 
         &*& distinct(snd_list(append(vals, cons(pair(key, value), nil)))) == true;
{
    switch(vals) {
        case nil:
        case cons(val0, vals0):
            maintain_distinct_append(key, value, vals0);
            maintain_distinct_append_helper(key, value, val0, vals0);
    }
}
@*/

public class RegisterSocketJob {
    SelectableChannel channel;
    Runnable command;
    int ops;
    
    public void execute(Selector selector, IdentityHashMap commands) throws ClosedChannelException /*@ ensures true; @*/
    /*@ requires registersocketjob(this) &*& selector != null &*& selector(selector, ?keys, nil, ?s) &*& commands != null 
    	    &*& Commands(commands, ?val)
            &*& foreach(fst_list(remove_all(nil, keys)), selectionkey_wrapper(selector)) &*& foreach(snd_list(remove_all(nil, keys)), @channel_wrapper)
            &*& not_null(fst_list(remove_all(nil, keys))) == true &*& not_null(snd_list(remove_all(nil, keys))) == true
            &*& keys_equals_map(remove_all(nil, keys), val) == true &*& distinct(snd_list(remove_all(nil, keys))) == true &*& distinct(fst_list(remove_all(nil, keys))) == true; @*/
    /*@ ensures selector(selector, ?keys2, nil, s) &*& Commands(commands, ?val2)
            &*& foreach(fst_list(remove_all(nil, keys2)), selectionkey_wrapper(selector)) &*& foreach(snd_list(remove_all(nil, keys2)), @channel_wrapper)
            &*& not_null(fst_list(remove_all(nil, keys2))) == true &*& not_null(snd_list(remove_all(nil, keys2))) == true
            &*& keys_equals_map(remove_all(nil, keys2), val2) == true &*& distinct(snd_list(remove_all(nil, keys2))) == true &*& distinct(fst_list(remove_all(nil, keys2))) == true; @*/
    {
        //@ open registersocketjob(this);

        SelectableChannel channel = this.channel;
        Runnable command = this.command;
         
        //@ contains_list(channel, val, remove_all(nil, keys));

        //@ open Commands(commands, val);

        channel.register(selector, ops);
        //@ assert selectionkey(?selKey, channel, selector); 

        /*@
        if(contains_key(selKey, remove_all(nil, keys)) == true) {
            contains_true_equals_keys_vals(selKey, channel, remove_all(nil, keys), val);
        }
        @*/

        commands.put(channel, command);

        /*@  
        if(contains_key(channel, val) == false) {
            close selectionkey_wrapper(selector)(selKey);
            
            close foreach(nil, selectionkey_wrapper(selector));
            close foreach(cons(selKey, nil), selectionkey_wrapper(selector));
            foreach_append(fst_list(remove_all(nil, keys)), cons(selKey, nil));

	    close channel_wrapper(channel);
	    
            close foreach(nil, @channel_wrapper);
            close foreach(cons(channel, nil), @channel_wrapper);
            foreach_append(snd_list(remove_all(nil, keys)), cons(channel, nil));

            close wrapper(pair(channel, command));
            close foreach(nil, @wrapper);
            close foreach(cons(pair(channel, command), nil), @wrapper);
            foreach_append(val, cons(pair(channel, command), nil));
            
            convert_appends(selKey, channel, keys);
            
            contains_key_to_mem(false, selKey, keys);
            contains_key_to_mem(false, channel, val);

            update_append_equals_chunk(selKey, channel, command, remove_all(nil, keys), val);
            
            maintain_distinct_append(selKey, channel, remove_all(nil, keys));
        }
        @*/  
	
        //@ close Commands(commands, _);  
    }
}
