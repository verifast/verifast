package gameserver;

import java.io.*;
import java.net.*;
import java.nio.*;
import java.nio.channels.*;
import java.util.*;
import java.util.concurrent.*;

/*@
predicate GameServerTemp(GameServer server) =
    server.exec |-> ?exec
    &*& server.selector |-> ?selector
    &*& server.games |-> ?games
    &*& server.semaGames |-> ?semaGames;

predicate GameServer(GameServer server) =
    server.exec |-> ?exec &*& exec!= null &*& [_]executor(exec)
    &*& server.selector |-> ?selector &*& selector != null
    &*& server.games |-> ?games &*& games!= null
    &*& server.semaGames |-> ?semaGames &*& semaGames != null &*& [_]semaphore_simple(semaGames, Games_ctor(games));
    
predicate_family socket_command(Class index)(Runnable command, SelectableChannel socket); 

typedef lemma void socket_command_to_runnable(Class index)();
    requires socket_command(index)(?command, ?channel) &*& channel(channel, 0);
    ensures thread_run_pre(index)(command, _);   

predicate wrapper(pair<SelectableChannel, Runnable> v) = 
    socket_command(snd(v).getClass())(snd(v), fst(v)) 
    &*& is_socket_command_to_runnable(?lemmaPointer, snd(v).getClass());

predicate Commands(Map commands, list<pair<SelectableChannel, Runnable> > val) = 
    foreach(val, @wrapper) &*& map(commands, val);
  
predicate_ctor Jobs_ctor(List jobs)() = 
    foreach(?val, @registersocketjob) &*& not_null(val) == true
    &*& list(jobs, val); 
    
predicate channel_wrapper(SelectableChannel channel) = channel(channel, 1);
predicate_ctor selectionkey_wrapper(Selector selector)(SelectionKey key) = selectionkey(key, ?channel, selector);

fixpoint boolean keys_equals_map<u, t, v>(list<pair<u, t> > keys, list<pair<t, v> > val) {
    return snd_list(keys) == fst_list(val);
}

lemma void generate_equals_chunk(Selector selector, Map map)
    requires selector(selector, ?keys, ?cancelledKeys, ?s) &*& map(map, ?val) &*& keys == nil &*& val == nil;
    ensures selector(selector, keys, cancelledKeys, s) &*& map(map, val) &*& keys_equals_map<Object, Object, Object>(keys, val) == true;
{}

lemma void update_append_equals_chunk<u, t, v>(u key, t channel, v command, list<pair<u, t> > keys, 
			list<pair<t, v> > vals)
    requires keys_equals_map(keys, vals) == true;
    ensures keys_equals_map(append(keys, cons(pair(key, channel), nil)), append(vals, cons(pair(channel, command), nil))) == true;
{	
	switch (keys) {
        	case nil: 
        	case cons(key0, keys0):
        		tails_equal(keys, vals);
        		update_append_equals_chunk(key, channel, command, keys0, tail(vals));
        		switch (vals) {
					case nil:
					case cons(val0, vals0):
		    	}	
    	}
}

lemma void mem_snd_list_helper<t, u>(pair<t, u> selectedKey, list<pair<t, u> > keys)
    requires mem(selectedKey, keys) == true;
    ensures mem(snd(selectedKey), snd_list(keys)) == true;
{
	switch (keys) {
		case nil:
		case cons(key0, keys0):
		if(key0 == selectedKey) {
		}
		else {
			mem_snd_list(selectedKey, keys0);
		}
			
	}
}

lemma void update_remove_equals_chunk_helper(SelectionKey skey, SelectableChannel channel, pair<SelectionKey, SelectableChannel> key, 
		list<pair<SelectionKey, SelectableChannel> > keys)
    requires snd(key) == channel &*& channel == in_map(skey, keys) &*& mem(key, keys) == true
    		&*& distinct(snd_list(keys)) == true &*& contains_key(skey, keys) == true;
    ensures fst(key) == skey;
{
	switch (keys) {
        	case nil: 
        	case cons(key0, keys0):
        		switch (key) {
        			case pair(a, b):
        				switch (key0) {
						case pair(c, d):
							if(c == skey) {
								if(a == skey) {
								}
								else {
									mem_snd_list(key, keys0);
								}
							}
							else {
								helper(skey, channel, key0, keys0);
									
								update_remove_equals_chunk_helper(skey, channel, key, keys0);
							}
					}
        		}		
        }
}


lemma void update_remove_equals_chunk(SelectionKey key, SelectableChannel channel, Runnable command, list<pair<SelectionKey, SelectableChannel> > keys, 
		list<pair<SelectableChannel, Runnable> > vals)
    requires keys_equals_map(keys, vals) == true &*& distinct(snd_list(keys)) == true &*& key != null &*& channel != null
    		&*& channel == in_map(key, keys) &*& command == in_map(channel, vals) &*& contains_key(key, keys) == true;
    ensures keys_equals_map(remove(pair(key, channel), keys), remove(pair(channel, command), vals)) == true;
{   	
    	switch (keys) {
        	case nil: 
        	case cons(key0, keys0):
        		switch (vals) {
				case nil:
				case cons(val0, vals0):
					if(snd(key0) == channel) {
						update_remove_equals_chunk_helper(key, channel, key0, keys);
	
						fst_snd_equal_pair(key, channel, key0);
						fst_snd_equal_pair(channel, command, val0);
					}
					else {
						tails_equal(keys, vals);
						update_remove_equals_chunk(key, channel, command, keys0, vals0);
					}
		    	}
    	}
}
@*/

public class GameServer {
    Executor exec;
    Selector selector;
    Games games;
    Semaphore semaGames;

    public void writeToSocket(String line, SocketChannel channel) throws IOException /*@ ensures true; @*/
    //@ requires line != null &*& channel != null &*& channel(channel, 0) &*& [?f]GameServer(this);
    //@ ensures channel(channel, 0) &*& [f]GameServer(this);
    {
        byte[] l = line.getBytes();
        ByteBuffer buffer = ByteBuffer.allocate(l.length);
        buffer.put(l);
        buffer.flip();
        channel.write(buffer);

        if(buffer.hasRemaining()) {
            Selector selector = Selector.open();
            SelectionKey selKey = channel.register(selector, SelectionKey.OP_WRITE);

            while(buffer.hasRemaining())
            /*@ invariant bytebuffer(buffer, l.length, l.length, _) &*& selector(selector, ?keys, nil, ?s) &*& channel(channel, 1) 
            	&*& selectionkey(selKey, channel, selector) &*& set(s, _); @*/
            {
                selector.select();

                if (selKey.isValid() && selKey.isWritable()) {
                    channel.write(buffer);
                }
            }

            selKey.cancel();
        }
    }

    public void startServer()
    //@ requires GameServerTemp(this);
    //@ ensures true;
    {
        //@ open GameServerTemp(this);
        try {
            ServerSocketChannel ssChannel = ServerSocketChannel.open();
            ssChannel.configureBlocking(false);
            ServerSocket socket = ssChannel.socket();

            //@ cast_to_serversocket(ssChannel, socket);
            socket.bind(new InetSocketAddress(1234));
            //@ cast_to_serversocketchannel(ssChannel, socket);

            Games games = new Games();
            games.count = 0;
            games.head = null;
            this.games = games;

            //@ close Game(null, 0);
            //@ close Games(games);
            //@ close Games_ctor(games)();
            //@ close n_times(0, Games_ctor(games));
            //@ close n_times(1, Games_ctor(games));
            Semaphore semaGames = new Semaphore(1);
            this.semaGames = semaGames;

            IdentityHashMap commands = new IdentityHashMap();

            Executor exec = Executors.newFixedThreadPool(2);
            this.exec = exec;
            //@ leak [1/2]executor(exec);

            Selector selector = Selector.open();
            this.selector = selector;
            
            //@ generate_equals_chunk(selector, commands);

            ssChannel.register(selector, SelectionKey.OP_ACCEPT);
            
            //@ close foreach(nil, selectionkey_wrapper(selector));
            //@ close foreach(nil, channel_wrapper);

            //@ assert selectionkey(?selKey, ssChannel, selector);
            //@ close selectionkey_wrapper(selector)(selKey);
            
            //@ close foreach(nil, selectionkey_wrapper(selector));
            //@ close foreach(cons(selKey, nil), selectionkey_wrapper(selector));
            //@ foreach_append(fst_list(nil), cons(selKey, nil));
            
            //@ close channel_wrapper(ssChannel);
            
            //@ close foreach(nil, channel_wrapper);
            //@ close foreach<SelectableChannel>(cons(ssChannel, nil), channel_wrapper);
            //@ foreach_append<SelectableChannel>(snd_list(nil), cons(ssChannel, nil));
            
            //@ close foreach(nil, wrapper);

            List jobs = new ArrayList();

            //@ close foreach(nil, registersocketjob);
            //@ close Jobs_ctor(jobs)();
            //@ close n_times(0, Jobs_ctor(jobs));
            //@ close n_times(1, Jobs_ctor(jobs));

            Semaphore semaJobs = new Semaphore(1);

            AcceptNewClient ssCommand = new AcceptNewClient();
            ssCommand.gameServer = this;
            ssCommand.jobs = jobs;
            ssCommand.semaJobs = semaJobs;
            ssCommand.ssChannel = ssChannel;
            ssCommand.selector = selector;
            
            //@ create_semaphore_simple(semaGames);
            //@ leak [1/2]semaphore_simple(semaGames, Games_ctor(games));
            
            //@ close GameServer(this);
            //@ leak [1/2]GameServer(this);
            //@ semaphore_split(semaJobs);
            
            //@ close socket_command(AcceptNewClient.class)(ssCommand, ssChannel);
            //@ produce_lemma_function_pointer_chunk(AcceptNewClient_to_runnable) : socket_command_to_runnable(AcceptNewClient.class)() { call(); };

            //@ close wrapper(pair(ssChannel, ssCommand));
            //@ close foreach(nil, @wrapper);
            //@ close foreach<pair<SelectableChannel, Runnable> >(cons(pair(ssChannel, ssCommand), nil), @wrapper);
            //@ foreach_append<pair<SelectableChannel, Runnable> >(nil, cons(pair(ssChannel, ssCommand), nil));
            
            commands.put(ssChannel, ssCommand);                        
            
            //@ close Commands(commands, _);            

            ChannelManager command = new ChannelManager();
            command.gameServer = this;
            command.selector = selector;
            command.jobs = jobs;
            command.semaJobs = semaJobs;
            command.commands = commands;

            Thread t = new Thread(command);
            t.setPriority(Thread.MAX_PRIORITY);

            //@ close ChannelManager(command);
            //@ close thread_run_pre(ChannelManager.class)(command, unit);
            t.start();

        } catch (IOException ex) {}
    }

    public void joinGameCore(SocketChannel socket, Semaphore semaGames, Games games, Game joinedGame, List jobs, Semaphore semaJobs) throws IOException /*@ ensures true; @*/ , InterruptedException /*@ ensures true; @*/
    /*@ requires socket != null &*& channel(socket, 0) &*& joinedGame != null &*& joinedGame.name |-> ?name
    &*& joinedGame.socket |-> ?s &*& s != null &*& channel(s, 0) &*& jobs != null
    &*& joinedGame.next |-> ?next &*& [?f]GameServer(this) &*& games != null &*& semaJobs != null &*& semaphore(?f2, semaJobs, ?p, Jobs_ctor(jobs)); @*/
    //@ ensures true;
    {
        SocketChannel joinedGameSocket = joinedGame.socket;

        writeToSocket("\r\nYou have joined " + joinedGame.name + ".\r\n", socket);
        writeToSocket("\r\nAnother player joined your game.\r\n", joinedGameSocket);

        //@ open [f]GameServer(this);

        GameStatus status = new GameStatus();
        status.player1 = socket;
        status.player2 = joinedGameSocket;
        status.player1Choice = -1;
        status.player1Choice = -1;
        status.player1HasPlayed = false;
        status.player2HasPlayed = false;
        
        //@ close gamestatus(status, socket, joinedGameSocket);

        PlayGameStep1 command = new PlayGameStep1();
        command.gameServer = this;
        command.status = status;
        command.selector = selector;
        command.jobs = jobs;
        command.semaJobs = semaJobs;

        Executor exec = this.exec;

        //@ close [f]GameServer(this);
        //@ close PlayGameStep1(command);
        //@ close thread_run_pre(PlayGameStep1.class)(command, unit);
        exec.execute(command);
    }
}
