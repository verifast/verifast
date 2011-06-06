package gameserver;

import java.io.*;
import java.nio.*;
import java.nio.channels.*;
import java.util.*;
import java.util.concurrent.*;

/*@
predicate_ctor key_channel_collection(Selector selector)(list<pair<SelectionKey, SelectableChannel> > keyPairs) = 
	foreach(fst_list(keyPairs), selectionkey_wrapper(selector)) &*& foreach(snd_list(keyPairs), @channel_wrapper)
    	&*& distinct(snd_list(keyPairs)) == true &*& distinct(fst_list(keyPairs)) == true
    	&*& not_null(fst_list(keyPairs)) == true &*& not_null(snd_list(keyPairs)) == true;
    	
predicate ChannelManager(ChannelManager command) = 
    command.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer)
    &*& command.selector |-> ?selector &*& selector != null &*& selector(selector, ?keys, ?cancelledKeys, ?s) &*& set(s, _)
    &*& command.commands |-> ?commands &*& commands != null &*& Commands(commands, ?val)
    &*& command.jobs |-> ?jobs &*& jobs != null
    &*& command.semaJobs |-> ?semaJobs &*& semaJobs != null &*& semaphore(?f, semaJobs, ?p, Jobs_ctor(jobs))
    &*& foreach(fst_list(remove_all(cancelledKeys, keys)), selectionkey_wrapper(selector)) &*& foreach(snd_list(remove_all(cancelledKeys, keys)), @channel_wrapper)
    &*& distinct(snd_list(remove_all(cancelledKeys, keys))) == true &*& distinct(fst_list(remove_all(cancelledKeys, keys))) == true
    &*& not_null(fst_list(remove_all(cancelledKeys, keys))) == true &*& not_null(snd_list(remove_all(cancelledKeys, keys))) == true
    &*& keys_equals_map(remove_all(cancelledKeys, keys), val) == true;

predicate_family_instance thread_run_pre(ChannelManager.class)(ChannelManager run, any info) = 
    ChannelManager(run);
predicate_family_instance thread_run_post(ChannelManager.class)(ChannelManager run, any info) = 
    ChannelManager(run); 

lemma void equalize_removes(Object key, Object value, list<pair<Object, Object> > keys)
requires mem(key, fst_list(keys)) == true &*& value == in_map(key, keys) 
			&*& distinct(fst_list(keys)) == true &*& distinct(snd_list(keys)) == true;
ensures remove(key, fst_list(keys)) == fst_list(remove(pair(key, value), keys)) 
		&*& remove(value, snd_list(keys)) == snd_list(remove(pair(key, value), keys));
{
	switch (keys) {
		case nil:
		case cons(key0, keys0):
			if(fst(key0) == key && snd(key0) == value) {
				fst_snd_equal_pair(key, value, key0);		
			}
			else if(fst(key0) != key && snd(key0) == value) {
				mem_fst_to_mem_snd(key, value, keys0);
			}
			else {
				equalize_removes(key, value, keys0);	
			}
	}
}

lemma void subset_safe_remove_helper<t>(t selectedKey, t x, list<t> keys)
requires selectedKey != x &*& mem(selectedKey, keys) == true;
ensures mem(selectedKey, remove(x, keys)) == true;
{
	switch (keys) {
		case nil:
		case cons(key0, keys0):
			if(key0 == selectedKey) {
			}
			else {
				subset_safe_remove_helper(selectedKey, x, keys0);
			}
	}
}

lemma void subset_safe_remove<t>(t x, list<t> keys, list<t> selectedKeys)
requires subset(keys, selectedKeys) == true &*& mem(x, selectedKeys) == false;
ensures subset(remove(x, keys), selectedKeys) == true;
{
	switch (selectedKeys) {
		case nil:
		case cons(selectedKey0, selectedKeys0):
			subset_safe_remove(x, keys, selectedKeys0);
			subset_safe_remove_helper(selectedKey0, x, keys);
	}
}

lemma void maintain_mem<t>(t x, t y, list<t> selectedKeys)
requires mem(x, selectedKeys) == true &*& y != x;
ensures mem(x, remove(y, selectedKeys)) == true;
{
	switch (selectedKeys) {
		case nil:
		case cons(selectedKey0, selectedKeys0):
			if(selectedKey0 == x) {
			}
			else {
				maintain_mem(x, y, selectedKeys0);
			}
			
	}
}

lemma void maintain_subset_single_remove_nth<t>(int index, t value, list<t> superList, list<t> subList)
requires value == nth(index, subList) 
			&*& subset(superList, subList) == true &*& 0 <= index &*& index < length(subList);
ensures subset(superList, remove_nth(index, subList)) == true;
{
	switch (subList) {
		case nil:
		case cons(sub0, subList0):
			if(index == 0) {
			}
			else {
				maintain_subset_single_remove_nth(index-1, value, superList, subList0);
			}
	}
}

lemma void maintain_distinct_helper(Object skey, Object value, pair<Object, Object> key, list<pair<Object, Object> > keys)
requires mem(fst(key), fst_list(keys)) == false &*& mem(snd(key), snd_list(keys)) == false;
ensures mem(fst(key), fst_list(remove(pair(skey, value), keys))) == false &*& mem(snd(key), snd_list(remove(pair(skey, value), keys))) == false;
{
	switch (keys) {
		case nil:
		case cons(key0, keys0):
			maintain_distinct_helper(skey, value, key, keys0);
	}
}

lemma void maintain_distinct(Object key, Object value, list<pair<Object, Object> > keys)
requires distinct(fst_list(keys)) == true &*& distinct(snd_list(keys)) == true 
		&*& mem(key, fst_list(keys)) == true
		&*& value == in_map(key, keys);
ensures distinct(fst_list(remove(pair(key, value), keys))) == true 
		&*& distinct(snd_list(remove(pair(key, value), keys))) == true;
{
	switch (keys) {
		case nil:
		case cons(key0, keys0):
			if(fst(key0) == key && snd(key0) == value) {
				fst_snd_equal_pair(key, value, key0);		
			}
			else if(fst(key0) != key && snd(key0) == value) {
				mem_fst_to_mem_snd(key, value, keys0);
			}
			else if(fst(key0) == key && snd(key0) != value) {
				mem_fst_to_mem_snd(key, value, keys0);
			}
			else {
				maintain_distinct(key, value, keys0);
				maintain_distinct_helper(key, value, key0, keys0);
			}
	}
}

lemma void tails_equal_helper<u, t, v>(list<pair<u, t> > keys, list<pair<t, v> > vals)
requires keys_equals_map(keys, vals) == true &*& keys == nil;
ensures vals == nil;
{
	switch (vals) {
		case nil:
		case cons(val0, vals0):
			tails_equal_helper(keys, vals0);			
	}
}

lemma void tails_equal<u, t, v>(list<pair<u, t> > keys, list<pair<t, v> > vals)
requires keys_equals_map(keys, vals) == true;
ensures keys_equals_map(tail(keys), tail(vals)) == true;
{
	switch (keys) {
		case nil:
			tails_equal_helper(keys, vals);
		case cons(key0, keys0):
			switch (vals) {
				case nil:
				case cons(val0, vals0):
					tails_equal(keys0, vals0);
			}		
	}
}

lemma void mem_subset<t>(t key, list<t> superList, list<t> subList)
    requires mem(key, subList) == true &*& subset(superList, subList) == true;
    ensures mem(key, superList) == true;
{
	switch (subList) {
		case nil:
		case cons(sub0, subList0):
			if(sub0 == key) {
			}
			else {
				mem_subset(key, superList, subList0);
			}
	}
}

lemma void not_null_subset(list<Object> superList, list<Object> subList)
    requires not_null(superList) == true &*& subset(superList, subList) == true;
    ensures not_null(subList) == true;
{
	switch (subList) {
		case nil: 			
		case cons(sub0, subList0):
			if(sub0 == null) {
				element_not_null(sub0, superList);
			}
			else {	
				not_null_subset(superList, subList0);
			}		
	}
}

lemma void mem_contains_key(Object key, list<pair<Object, Object> > vals)
requires mem(key, fst_list(vals)) == true;
ensures contains_key(key, vals) == true;
{
	switch (vals) {
		case nil:
		case cons(val0, vals0):
			if(fst(val0) == key) {		
			}
			else {
				mem_contains_key(key, vals0);
			}			
	}
}

lemma void remove_nth_maintains_distinct_helper<t>(int index, t value, list<t> vals)
requires mem(value, vals) == false;
ensures mem(value, remove_nth(index-1, vals)) == false;
{
	switch (vals) {
		case nil:
		case cons(val0, vals0):
			remove_nth_maintains_distinct_helper(index-1, value, vals0);
	}
}

lemma void remove_nth_maintains_distinct<t>(int index, list<t> vals)
requires distinct(vals) == true &*& 0 <= index &*& index < length(vals);
ensures distinct(remove_nth(index, vals)) == true;
{
	switch (vals) {
		case nil:
		case cons(val0, vals0):
			if(index == 0) {
			}
			else {
				remove_nth_maintains_distinct(index-1, vals0);
				remove_nth_maintains_distinct_helper(index, val0, vals0);
			}
	}
}

lemma void contains_true_equals_keys_vals(SelectionKey key, SelectableChannel channel, list<pair<SelectionKey, SelectableChannel> > keys, 
            list<pair<SelectableChannel, Runnable> > vals)
 requires contains_key(key, keys) == true &*& keys_equals_map(keys, vals) == true &*& in_map(key, keys) == channel;
 ensures contains_key(channel, vals) == true;
{
    switch(keys) {
        case nil:
        case cons(key0, keys0):
        	if(fst(key0) == key) {
        		switch(vals) {
				case nil:
				case cons(val0, vals0):
			}
        	}
        	else {
        		switch(vals) {
				case nil: assert(contains_key(channel, vals) == true);
				case cons(val0, vals0):
					tails_equal(keys, vals);
				    	contains_true_equals_keys_vals(key, channel, keys0, vals0);
			}
        	}
    }
}

lemma void key_not_in_head_single<t>(int index, t key, list<t> vals)
 requires nth(index, vals) == key &*& 0 < index &*& index < length(vals) &*& distinct(vals) == true;
 ensures head(vals) != key;
{
	switch (vals) {
		case nil:
		case cons(val0, vals0):	
			mem_nth(index-1, vals0);	
	}
}

lemma void remove_nth_to_remove(int index, Object key, list<Object> iter_vals)
requires key == nth(index, iter_vals) &*& 0 <= index &*& index < length(iter_vals) &*& distinct(iter_vals) == true;
ensures remove_nth(index, iter_vals) == remove(key, iter_vals);
{
	switch(iter_vals) {
		case nil:
		case cons(iter_val0, iter_vals0):
			if(index == 0) {
			}
			else if(iter_val0 == key) {
				key_not_in_head_single(index, key, iter_vals);
			}
			else {
				remove_nth_to_remove(index-1, key, iter_vals0);
			}
	}
}

lemma void maintain_subset_selected_keys_iter_vals(Object key, list<Object> superList, list<Object> subList)
requires mem(key, subList) == true &*& subset(superList, subList) == true &*& distinct(subList) == true;
ensures subset(remove(key, superList), remove(key, subList)) == true;
{
	switch (subList) {
		case nil:
		case cons(sub0, subList0):
			if(sub0 == key) {
				subset_safe_remove(sub0, superList, remove(key, subList));
			}
			else {
				maintain_subset_selected_keys_iter_vals(key, superList, subList0);
				maintain_mem(sub0, key, superList);
			}
	}
}

lemma void helper(Object skey, Object channel, pair<Object, Object> key, list<pair<Object, Object> > keys)
    requires contains_key(skey, keys) == true &*& channel == in_map(skey, keys);
    ensures mem(in_map(skey, keys), snd_list(keys)) == true;
{  
	switch (keys) {
        	case nil: 
        	case cons(key0, keys0):
        		if(fst(key0) == skey) {
        		}
        		else {
        			helper(skey, channel, key, keys0);
        		}
        		
        }
}

lemma void trans_subset<t>(list<t> list1, list<t> list2, list<t> list3)
requires subset(list1, list2) == true &*& subset(list2, list3) == true;
ensures subset(list1, list3) == true;
{
	switch(list3) {
		case nil:
		case cons(l0, list0):
			mem_subset(l0, list1, list2);	
			trans_subset(list1, list2, list0);	
	}
}

lemma void in_map_remove_all_helper<t, u>(t key, u channel, pair<t, u> cKey, list<pair<t, u> > rKeys)
requires channel == in_map(key, rKeys) &*& fst(cKey) != key;
ensures channel == in_map(key, remove(cKey, rKeys));
{
	switch(rKeys) {
		case nil: 
        	case cons(rKey0, rKeys0):
        		if(fst(rKey0) == key) {
        		}
        		else {
        			in_map_remove_all_helper(key, channel, cKey, rKeys0);
        		}
        }
}

lemma void in_map_remove_all<t, u>(t key, u channel, list<pair<t, u> > keys, list<pair<t, u> > cancelledKeys)
requires contains_key(key, cancelledKeys) == false &*& channel == in_map(key, keys);
ensures channel == in_map(key, remove_all(cancelledKeys, keys));
{
	switch(cancelledKeys) {
		case nil: 
        	case cons(cKey0, cKeys0):
        		if(fst(cKey0) == key) {
        		}
        		else {
        			in_map_remove_all(key, channel, keys, cKeys0);
        			in_map_remove_all_helper(key, channel, cKey0, remove_all(cKeys0, keys));
        		}
	}
}
@*/

public class ChannelManager implements Runnable {
    Selector selector;
    GameServer gameServer;
    IdentityHashMap commands;
    List jobs;
    Semaphore semaJobs;

    public void run()
    //@ requires thread_run_pre(ChannelManager.class)(this, ?info);
    //@ ensures thread_run_post(ChannelManager.class)(this, info);
    {
        while (true)
        //@ invariant thread_run_pre(ChannelManager.class)(this, info);
        {
            try {
                //@ open thread_run_pre(ChannelManager.class)(this, info);
                //@ open ChannelManager(this);

                Selector selector = this.selector;	
                selector.select();           

                Semaphore semaJobs = this.semaJobs;
                List jobs = this.jobs;
                IdentityHashMap commands = this.commands;
                GameServer gameServer = this.gameServer;
                //@ open [?f]GameServer(gameServer);
                Executor exec = gameServer.exec;
                Semaphore semaGames = gameServer.semaGames;
                //@ close [f]GameServer(gameServer);

                semaJobs.acquire();
                //@ open Jobs_ctor(jobs)();

                if(jobs.size() > 0) {
                    Iterator it = jobs.iterator();
 			
 		//@ assert selector(selector, _, nil, ?s);
 
                    while (it.hasNext()) 
                    /*@ invariant foreach(?val, @registersocketjob) &*& iter(it, 1, jobs, list_wrapper, val, ?index) &*& 0 == index &*& 0 <= length(val) 
                        &*& selector(selector, ?ks, nil, s) &*& not_null(val) == true &*& Commands(commands, ?val2)
                        &*& foreach(fst_list(remove_all(nil, ks)), selectionkey_wrapper(selector)) &*& foreach(snd_list(remove_all(nil, ks)), @channel_wrapper)
                        &*& not_null(fst_list(remove_all(nil, ks))) == true &*& not_null(snd_list(remove_all(nil, ks))) == true
                        &*& keys_equals_map(remove_all(nil, ks), val2) == true &*& distinct(snd_list(remove_all(nil, ks))) == true 
                        &*& distinct(fst_list(remove_all(nil, ks))) == true; @*/
                    {
                        Object o = it.next();
                        RegisterSocketJob job = (RegisterSocketJob) o;
                        
                        //@ foreach_remove_nth(index, val);
                        
                        it.remove();
                        
                        //@ list_not_null(index, val);
                        try { 
                            job.execute(selector, commands);
                        }
                        catch (IOException e) {
                            throw new RuntimeException();
                        }
                    }
                    
                    //@ iter_dispose(it);
                    //@ open list_wrapper(jobs, val);
                    
                    //@ close Jobs_ctor(jobs)();
                    semaJobs.release();
                    //@ close ChannelManager(this);
                    
                }
                else {
                    //@ close Jobs_ctor(jobs)();
                    semaJobs.release();

                    Set s = selector.selectedKeys();
 			//@ assert selector(selector, ?keys_, ?cancelledKeys_, s);
			//@ assert set(s, ?selectedKeys_);


                    Iterator it = s.iterator();
                    
                    //@ assert iter(it, 1, s, set_wrapper, ?iter_vals_, _);
                    
                    //@ trans_subset<Object>(fst_list(remove_all(cancelledKeys_, keys_)), selectedKeys_, iter_vals_);

                    while (it.hasNext())
                    /*@ invariant selector(selector, ?keys, ?cancelledKeys, s)
                    	&*& foreach(fst_list(remove_all(cancelledKeys, keys)), selectionkey_wrapper(selector)) 
                        &*& foreach(snd_list(remove_all(cancelledKeys, keys)), @channel_wrapper) &*& iter(it, 1, s, set_wrapper, ?iter_vals, ?index) 
                        &*& 0 == index &*& 0 <= length(iter_vals) &*& Commands(commands, ?val) 
                        &*& [_]executor(exec) &*& [_]GameServer(gameServer) &*& semaphore(?f2, semaJobs, ?p, Jobs_ctor(jobs))
                        &*& not_null(fst_list(remove_all(cancelledKeys, keys))) == true &*& not_null(snd_list(remove_all(cancelledKeys, keys))) == true
                        &*& distinct(iter_vals) == true
                        &*& distinct(fst_list(remove_all(cancelledKeys, keys))) == true &*& distinct(snd_list(remove_all(cancelledKeys, keys))) == true
                        &*& subset<Object>(fst_list(remove_all(cancelledKeys, keys)), iter_vals) == true 
                        &*& keys_equals_map(remove_all(cancelledKeys, keys), val) == true;
                        @*/
                    {
                        Object o = it.next();
                        SelectionKey selKey = (SelectionKey) o;
                        
                        it.remove();
                        
        		//@ mem_nth(index, iter_vals);
        		//@ mem_subset<Object>(selKey, fst_list(remove_all(cancelledKeys, keys)), iter_vals);
        		
        		//@ foreach_remove(selKey, fst_list(remove_all(cancelledKeys, keys)));
        		
        		//@ not_null_subset(fst_list(remove_all(cancelledKeys, keys)), iter_vals);
        		//@ element_not_null(selKey, iter_vals);
                        
                        //@ open selectionkey_wrapper(selector)(selKey);

                        SelectableChannel c = selKey.channel();
                        
                        //@ boolean undo = true;

                        if (selKey.isValid() && (selKey.isAcceptable() || selKey.isReadable())) {                        
                            	//@ mem_contains_key(selKey, remove_all(cancelledKeys, keys));
                            	//@ in_map_remove_all(selKey, c, keys, cancelledKeys);
                            	//@ contains_true_equals_keys_vals(selKey, c, remove_all(cancelledKeys, keys), val);
      				
      				//@ mem_pair_in_map(selKey, c, remove_all(cancelledKeys, keys));
      				//@ mem_pair_split(selKey, c, remove_all(cancelledKeys, keys));

                        	//@ foreach_remove(c, snd_list(remove_all(cancelledKeys, keys)));  
                            	
                            	//@ open channel_wrapper(c);
                                //@ open Commands(commands, _);
                                
                                selKey.cancel();
                                
                                //@ mem_contains_key(c, val);

                                Object command = commands.get(c);
                                Runnable run = (Runnable) command;

                                //@ mem_pair_in_map(c, run, val);
                                //@ foreach_remove(pair(c, run), val);
                                //@ open wrapper(pair(c, run));
                                //@ assert is_socket_command_to_runnable(?lemmaPointer, run.getClass());

                                commands.remove(c);

                                //@ remove_pair_from_list(c, run, val);
				
                                //@ lemmaPointer();

                                exec.execute(run);

                                //@ close Commands(commands, _);
                                
                                //@ undo = false;
                                
                                //@ update_remove_equals_chunk(selKey, c, run, remove_all(cancelledKeys, keys), val);
                                //@ equalize_removes(selKey, c, remove_all(cancelledKeys, keys));
                                //@ maintain_distinct(selKey, c, remove_all(cancelledKeys, keys));
                                //@ maintain_subset_selected_keys_iter_vals(selKey, fst_list(remove_all(cancelledKeys, keys)), iter_vals);
                            }
                            /*@
                            if(undo == true) { 
                            	close selectionkey_wrapper(selector)(selKey);
                                foreach_unremove(selKey, fst_list(remove_all(cancelledKeys, keys)));
                                
                                maintain_subset_single_remove_nth<Object>(index, selKey, fst_list(remove_all(cancelledKeys, keys)), iter_vals);
                            }
                            @*/
                            
                            //@ remove_nth_maintains_distinct(index, iter_vals);
                            
			    //@ mem_contains_key(selKey, remove_all(cancelledKeys, keys));

                            //@ remove_nth_to_remove(index, selKey, iter_vals);
                    }
                    //@ iter_dispose(it);
                    //@ open set_wrapper(s, iter_vals);		
		    
                    //@ close ChannelManager(this);
                }
            }
            catch (InterruptedException ex) {
                throw new RuntimeException();
            }
            catch (IOException e) {
                throw new RuntimeException();
            }

            //@ close thread_run_pre(ChannelManager.class)(this, info);
        }
    }
}
