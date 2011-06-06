
package gameserver;

import java.io.*;
import java.nio.channels.*;
import java.util.*;
import java.util.concurrent.*;

/*@
predicate_family_instance socket_command(AcceptNewClient.class)(AcceptNewClient command, ServerSocketChannel channel) = 
    command.ssChannel |-> channel &*& channel != null
    &*& command.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer)
    &*& command.jobs |-> ?jobs &*& jobs != null
    &*& command.selector |-> ?selector &*& selector != null
    &*& command.semaJobs |-> ?semaJobs &*& semaJobs != null &*& semaphore(?f, semaJobs, ?p, Jobs_ctor(jobs));

predicate_family_instance thread_run_pre(AcceptNewClient.class)(AcceptNewClient run, any info) = 
    run.ssChannel |-> ?channel &*& channel != null &*& channel(channel, 0)
    &*& run.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer)
    &*& run.jobs |-> ?jobs &*& jobs != null
    &*& run.selector |-> ?selector &*& selector != null
    &*& run.semaJobs |-> ?semaJobs &*& semaJobs != null &*& semaphore(?f, semaJobs, ?p, Jobs_ctor(jobs));

predicate_family_instance thread_run_post(AcceptNewClient.class)(AcceptNewClient run, any info) = 
    true;

lemma void AcceptNewClient_to_runnable()
    requires socket_command(AcceptNewClient.class)(?command, ?channel) &*& channel(channel, 0);
    ensures thread_run_pre(AcceptNewClient.class)(command, _);
{
    open socket_command(AcceptNewClient.class)(?command_, ?channel_);
    close thread_run_pre(AcceptNewClient.class)(command_, unit);
}

@*/
public class AcceptNewClient implements Runnable {

    ServerSocketChannel ssChannel;
    GameServer gameServer;
    List jobs;
    Semaphore semaJobs;
    Selector selector;

    public void run() 
    //@ requires thread_run_pre(AcceptNewClient.class)(this, ?info);
    //@ ensures thread_run_post(AcceptNewClient.class)(this, info);
    {
        //@ open thread_run_pre(AcceptNewClient.class)(this, info);
        try {
            Semaphore semaJobs = this.semaJobs;
            List jobs = this.jobs;

            GameServer gameServer = this.gameServer;
            //@ open [?f]GameServer(gameServer);
            Executor exec = gameServer.exec;
            //@ close [f]GameServer(gameServer);

            SocketChannel sChannel = ssChannel.accept();
            sChannel.configureBlocking(false);
            DisplayMenu command = new DisplayMenu();
            command.gameServer = gameServer;
            command.socket = sChannel;
            command.jobs = jobs;
            command.semaJobs = semaJobs;
            
            //@ semaphore_split(semaJobs);
            //@ close DisplayMenu(command, sChannel);
            //@ close thread_run_pre(DisplayMenu.class)(command, unit);
            
            exec.execute(command);
            
            SelectableChannel c = (SelectableChannel) ssChannel;
            
            AcceptNewClient ssCommand = new AcceptNewClient();
            ssCommand.gameServer = gameServer;
            ssCommand.jobs = jobs;
            ssCommand.semaJobs = semaJobs;
            ssCommand.ssChannel = ssChannel;
            ssCommand.selector = selector;

            RegisterSocketJob job = new RegisterSocketJob();
            job.channel = c;
            job.command = ssCommand;
            job.ops = SelectionKey.OP_ACCEPT;
            
            //@ semaphore_split(semaJobs);
            
                
            //@ close socket_command(AcceptNewClient.class)(ssCommand, ssChannel);
            //@ produce_lemma_function_pointer_chunk(AcceptNewClient_to_runnable) : socket_command_to_runnable(AcceptNewClient.class)() { call(); };

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
        catch (IOException ex) {
        }
        catch (InterruptedException ex) {
        }
        
        //@ close thread_run_post(AcceptNewClient.class)(this, info);
    }
}
