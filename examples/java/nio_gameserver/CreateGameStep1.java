package gameserver;

import java.io.*;
import java.nio.*;
import java.nio.channels.*;
import java.util.*;
import java.util.concurrent.*;

/*@
predicate CreateGameStep1(CreateGameStep1 command) = 
    command.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer)
    &*& command.socket |-> ?socket &*& socket!= null &*& channel(socket, 0)
    &*& command.jobs |-> ?jobs &*& jobs != null
    &*& command.semaJobs |-> ?semaJobs &*& semaJobs != null &*& semaphore(?f, semaJobs, ?p, Jobs_ctor(jobs));

predicate_family_instance thread_run_pre(CreateGameStep1.class)(CreateGameStep1 run, any info) = 
    CreateGameStep1(run);
predicate_family_instance thread_run_post(CreateGameStep1.class)(CreateGameStep1 run, any info) = 
    true;
@*/

public class CreateGameStep1 implements Runnable {
    SocketChannel socket;
    GameServer gameServer;
    List jobs;
    Semaphore semaJobs;

    public void run() 
    //@ requires thread_run_pre(CreateGameStep1.class)(this, ?info);
    //@ ensures thread_run_post(CreateGameStep1.class)(this, info);
    {
        //@ open thread_run_pre(CreateGameStep1.class)(this, info);
        //@ open CreateGameStep1(this);
        try {
            GameServer gameServer = this.gameServer;
            //@ open [?f]GameServer(gameServer);
            Executor exec = gameServer.exec;

            Semaphore semaGames = gameServer.semaGames;
            Games games = gameServer.games;
            SocketChannel socket = this.socket;
            Selector selector = gameServer.selector;
            
            //@ semaphore_simple_split(semaGames);

            semaGames.acquire();
            //@ open Games_ctor(games)();
            //@ open Games(games);

            if (games.count == Integer.MAX_VALUE) {
                //@ close Games(games);
                //@ close Games_ctor(games)();
                semaGames.release();
                //@ close [f]GameServer(gameServer);
                gameServer.writeToSocket("Insufficient space. Try again later.\r\n", socket);

                DisplayMenu command = new DisplayMenu();
                command.gameServer = gameServer;
                command.socket = socket;
                command.jobs = jobs;
                command.semaJobs = semaJobs;
                
                //@ close DisplayMenu(command, socket);
                //@ close thread_run_pre(DisplayMenu.class)(command, unit);                
                exec.execute(command);
            } 
            else {
                //@ close Games(games);
                //@ close Games_ctor(games)();
                semaGames.release();
                //@ close [f]GameServer(gameServer);
                gameServer.writeToSocket("Enter the name of your game.\r\n", socket);

                CreateGameStep2 command = new CreateGameStep2();
                command.gameServer = gameServer;
                command.socket = socket;
                
                //@ open [f]GameServer(gameServer);
                ReadString command2 = new ReadString();
                command2.run = command;
                command2.maxCharsToRead = Integer.MAX_VALUE;
                command2.readSoFar = new String();
                command2.buffer = ByteBuffer.allocate(50);
                command2.channel = socket;
                command2.gameServer = gameServer;
                command2.jobs = jobs;
                command2.semaJobs = semaJobs;
                
                //@ semaphore_split(semaJobs);
                
                //@ close [f]GameServer(gameServer);
                
                //@ close CreateGameStep2(command, socket);                
                //@ close readstringclient(CreateGameStep2.class)(command, socket);
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
        } 
        catch (InterruptedException ex) {}
        catch (IOException ex) {}
        
        //@ close thread_run_post(CreateGameStep1.class)(this, info);
    }
}
