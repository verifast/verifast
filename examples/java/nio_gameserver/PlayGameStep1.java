package gameserver;

import java.io.*;
import java.nio.*;
import java.nio.channels.*;
import java.util.*;
import java.util.concurrent.*;

/*@
predicate PlayGameStep1(PlayGameStep1 command) = 
    command.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer)
    &*& command.status |-> ?status &*& status != null &*& gamestatus(status, ?player1, ?player2) &*& channel(player1, 0) &*& channel(player2, 0)
    &*& command.selector |-> ?selector &*& selector != null
    &*& command.jobs |-> ?jobs &*& jobs != null
    &*& command.semaJobs |-> ?semaJobs &*& semaJobs != null &*& semaphore(?f, semaJobs, ?p, Jobs_ctor(jobs));

predicate_family_instance thread_run_pre(PlayGameStep1.class)(PlayGameStep1 run, any info) = 
    PlayGameStep1(run);
predicate_family_instance thread_run_post(PlayGameStep1.class)(PlayGameStep1 run, any info) = 
    true;
@*/
public class PlayGameStep1 implements Runnable {
    Selector selector;
    GameStatus status;
    GameServer gameServer;
    List jobs;
    Semaphore semaJobs;

    public void run() 
    //@ requires thread_run_pre(PlayGameStep1.class)(this, ?info);
    //@ ensures thread_run_post(PlayGameStep1.class)(this, info);
    {
        //@ open thread_run_pre(PlayGameStep1.class)(this, info);
        //@ open PlayGameStep1(this);
        try {
            GameStatus status = this.status;
            //@ open gamestatus(status, _, _);
            SocketChannel player1 = status.player1;
            SocketChannel player2 = status.player2;
            
            gameServer.writeToSocket("Enter a rock (0), paper (1) or scissors (2).\r\n", player1);
            gameServer.writeToSocket("Enter a rock (0), paper (1) or scissors (2).\r\n", player2);

            //@ close gamestatus(status, _, _);
            //@ close gamestatus_ctor(status, player1, player2)();
            //@ close n_times(0, gamestatus_ctor(status, player1, player2));
            //@ close n_times(1, gamestatus_ctor(status, player1, player2));
            Semaphore semaStatus = new Semaphore(1);
            
            PlayGameStep2 command1 = new PlayGameStep2();
            command1.gameServer = gameServer;
            command1.status = status;
            command1.semaStatus = semaStatus;
            command1.selector = this.selector;
            command1.jobs = jobs;
            command1.semaJobs = semaJobs;
            command1.playerID = 1;
            command1.socket = player1;

            ReadString readCommand1 = new ReadString();
            readCommand1.run = command1;
            readCommand1.maxCharsToRead = 1;
            readCommand1.readSoFar = new String();
            readCommand1.buffer = ByteBuffer.allocate(5);
            readCommand1.channel = player1;
            readCommand1.gameServer = gameServer;
            readCommand1.jobs = jobs;
            readCommand1.semaJobs = semaJobs;

            PlayGameStep2 command2 = new PlayGameStep2();
            command2.gameServer = gameServer;
            command2.status = status;
            command2.semaStatus = semaStatus;
            command2.selector = this.selector;
            command2.jobs = jobs;
            command2.semaJobs = semaJobs;
            command2.playerID = 2;
            command2.socket = player2;

            ReadString readCommand2 = new ReadString();
            readCommand2.run = command2;
            readCommand2.maxCharsToRead = 1;
            readCommand2.readSoFar = new String();
            readCommand2.buffer = ByteBuffer.allocate(5);
            readCommand2.channel = player2;
            readCommand2.gameServer = gameServer;
            readCommand2.jobs = jobs;
            readCommand2.semaJobs = semaJobs;
            
            GameServer gameServer = this.gameServer;
            //@ open [?f]GameServer(gameServer);

            //@ close [f]GameServer(gameServer);
            
            //@ close gamestatus_ctor_args(player1, player2);
            //@ close gamestatus_ctor_args(player1, player2);

            //@ semaphore_split(semaStatus);
            
	    //@ semaphore_split(semaJobs);
	    //@ semaphore_split(semaJobs);
	    //@ semaphore_split(semaJobs);
	    //@ semaphore_split(semaJobs);
            
            //@ close PlayGameStep2(command1, player1);
            //@ close PlayGameStep2(command2, player2);
            
            //@ close readstringclient(PlayGameStep2.class)(command1, player1);
            //@ close readstringclient(PlayGameStep2.class)(command2, player2);
            
            //@ close socket_command(ReadString.class)(readCommand1, player1);
            //@ produce_lemma_function_pointer_chunk(ReadString_to_runnable) : socket_command_to_runnable(ReadString.class)() { call(); };
            //@ close socket_command(ReadString.class)(readCommand2, player2);
            //@ produce_lemma_function_pointer_chunk(ReadString_to_runnable) : socket_command_to_runnable(ReadString.class)() { call(); };

            RegisterSocketJob job1 = new RegisterSocketJob();
            job1.channel = (SelectableChannel) player1;
            job1.command = readCommand1;
            job1.ops = SelectionKey.OP_READ;

            RegisterSocketJob job2 = new RegisterSocketJob();
            job2.channel = (SelectableChannel) player2;
            job2.command = readCommand2;
            job2.ops = SelectionKey.OP_READ;
            
            //@ close registersocketjob(job1);
            //@ close registersocketjob(job2);

            semaJobs.acquire();

            //@ open Jobs_ctor(jobs)();

            //@ assert foreach(?val5, registersocketjob);
            //@ close foreach(nil, @registersocketjob);
            //@ close foreach(cons(job1, nil), @registersocketjob);
            //@ foreach_append(val5, cons(job1, nil));
            
            //@ assert foreach(?val6, registersocketjob);
            //@ close foreach(nil, @registersocketjob);
            //@ close foreach(cons(job2, nil), @registersocketjob);
            //@ foreach_append(val6, cons(job2, nil));

            jobs.add(job1);
            jobs.add(job2);

            //@ close Jobs_ctor(jobs)();
            semaJobs.release();

            selector.wakeup();
        }
        catch (InterruptedException ex) {
        throw new RuntimeException();
        } 
        catch (IOException ex) {
        throw new RuntimeException();
        }
        //@ close thread_run_post(PlayGameStep1.class)(this, info);
    }
}
