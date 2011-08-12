package gameserver;

import java.io.*;
import java.nio.*;
import java.nio.channels.*;
import java.util.*;
import java.util.concurrent.*;

/*@
    
predicate DisplayMenu(DisplayMenu command, SocketChannel socket) = 
    command.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer)
    &*& command.socket |-> socket &*& socket != null
    &*& command.jobs |-> ?jobs &*& jobs != null
    &*& command.semaJobs |-> ?semaJobs &*& semaJobs != null &*& semaphore(?f, semaJobs, ?p, Jobs_ctor(jobs)); 

predicate_family_instance thread_run_pre(DisplayMenu.class)(DisplayMenu run, any info) = 
    DisplayMenu(run, ?socket) &*& channel(socket, 0);
predicate_family_instance thread_run_post(DisplayMenu.class)(DisplayMenu run, any info) = 
    true;
@*/
public class DisplayMenu implements Runnable {
    SocketChannel socket;
    GameServer gameServer;
    List jobs;
    Semaphore semaJobs;
    
    public void run()
    //@ requires thread_run_pre(DisplayMenu.class)(this, ?info);
    //@ ensures thread_run_post(DisplayMenu.class)(this, info);
    {
        //@ open thread_run_pre(DisplayMenu.class)(this, info);
        //@ open DisplayMenu(this, ?s);
        try {
            String output = "\nWhat would you like to do?\r\n";
            output += "1. Create a new game.\r\n";
            output += "2. Show all available games.\r\n";
            output += "3. Join an existing game.\r\n";
            output += "4. Select and join an existing game.\r\n";
            output += "5. Quit.\r\n";
            output += "6. Create a new game (optional).\r\n";
            gameServer.writeToSocket(output, socket);

            ProcessMenuInput command = new ProcessMenuInput();
            command.gameServer = gameServer;
            command.socket = socket;
            command.jobs = jobs;
            command.semaJobs = semaJobs;
            
            GameServer gameServer = this.gameServer;
            
            //@ open [?f]GameServer(gameServer);
            
            Selector selector = gameServer.selector;
            
            //@ close [f]GameServer(gameServer);

            ReadString command2 = new ReadString();
            command2.run = command;
            command2.maxCharsToRead = 1;
            command2.readSoFar = new String();
            command2.buffer = ByteBuffer.allocate(5);
            command2.channel = socket;
            command2.gameServer = gameServer;
            command2.jobs = jobs;
            command2.semaJobs = semaJobs;
            
            //@ semaphore_split(semaJobs);
            //@ semaphore_split(semaJobs);

            //@ close ProcessMenuInput(command, socket);
            
            //@ close readstringclient(ProcessMenuInput.class)(command, socket);
            //@ close socket_command(ReadString.class)(command2, socket);
            //@ produce_lemma_function_pointer_chunk(ReadString_to_runnable) : socket_command_to_runnable(ReadString.class)() { call(); };

            RegisterSocketJob job = new RegisterSocketJob();
            job.channel = (SelectableChannel) socket;
            job.command = command2;
            job.ops = SelectionKey.OP_READ;

            //@ close registersocketjob(job);

            semaJobs.acquire();

            //@ open Jobs_ctor(jobs)();

            //@ assert foreach(?val, registersocketjob);
            //@ close foreach(nil, @registersocketjob);
            //@ close foreach(cons(job, nil), @registersocketjob);
            //@ foreach_append(val, cons(job, nil));

            jobs.add(job);

            //@ close Jobs_ctor(jobs)();
            semaJobs.release();

            selector.wakeup();
        }
        catch (InterruptedException ex) {}
        catch (IOException ex) {}
        
        //@ close thread_run_post(DisplayMenu.class)(this, info);
    }
}
