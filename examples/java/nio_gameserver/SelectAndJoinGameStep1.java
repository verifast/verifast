package gameserver;

import java.io.*;
import java.nio.*;
import java.nio.channels.*;
import java.util.*;
import java.util.concurrent.*;

/*@
predicate SelectAndJoinGameStep1(SelectAndJoinGameStep1 command) = 
    command.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer) 
    &*& command.socket |-> ?socket &*& socket!= null &*& channel(socket, 0)
    &*& command.jobs |-> ?jobs &*& jobs != null
    &*& command.semaJobs |-> ?semaJobs &*& semaJobs != null &*& semaphore(?f, semaJobs, ?p, Jobs_ctor(jobs));

predicate_family_instance thread_run_pre(SelectAndJoinGameStep1.class)(SelectAndJoinGameStep1 run, any info) = 
    SelectAndJoinGameStep1(run);
predicate_family_instance thread_run_post(SelectAndJoinGameStep1.class)(SelectAndJoinGameStep1 run, any info) = 
    true;
@*/
public class SelectAndJoinGameStep1 implements Runnable {
    SocketChannel socket;
    GameServer gameServer;
    List jobs;
    Semaphore semaJobs;

    public void run() 
    //@ requires thread_run_pre(SelectAndJoinGameStep1.class)(this, ?info);
    //@ ensures thread_run_post(SelectAndJoinGameStep1.class)(this, info);
    {
        //@ open thread_run_pre(SelectAndJoinGameStep1.class)(this, info);
        //@ open SelectAndJoinGameStep1(this); 
        try {
            GameServer gameServer = this.gameServer;
            //@ open [?f]GameServer(gameServer);
            Executor exec = gameServer.exec;

            Semaphore semaGames = gameServer.semaGames;
            Games games = gameServer.games;
            Selector selector = gameServer.selector;

	    //@ semaphore_simple_split(semaGames);
            semaGames.acquire();
            //@ open Games_ctor(games)();
            //@ open Games(games);
            if (games.count == 0) {
                //@ close [f]GameServer(gameServer);
                gameServer.writeToSocket("No game is available.\r\n", socket);
                //@ open [f]GameServer(gameServer);
                //@ close Games(games);
                //@ close Games_ctor(games)();
                semaGames.release();

                DisplayMenu command = new DisplayMenu();
                command.gameServer = gameServer;
                command.socket = socket;
                command.jobs = jobs;
                command.semaJobs = semaJobs;

                //@ close [f]GameServer(gameServer);
                //@ close DisplayMenu(command, socket);
                //@ close thread_run_pre(DisplayMenu.class)(command, unit);

                exec.execute(command);
            } 
            else {
                //@ close [f]GameServer(gameServer);
                gameServer.writeToSocket("The following games are available.\r\n", socket);
                //@ open [f]GameServer(gameServer);
                showGamesHelper(socket, games.head, games.count);
                //@ close [f]GameServer(gameServer);
                gameServer.writeToSocket("Enter the number of the game you want to join (between 1 and " + String.valueOf(games.count) + ").\r\n", socket);
                
                //@ close Games(games);
                //@ close Games_ctor(games)();
                semaGames.release();

                SelectAndJoinGameStep2 command = new SelectAndJoinGameStep2();
                command.gameServer = gameServer;
                command.socket = socket;
                command.jobs = jobs;
                command.semaJobs = semaJobs;

                ReadString command2 = new ReadString();
                command2.run = command;
                command2.maxCharsToRead = 12;
                command2.readSoFar = new String();
                command2.buffer = ByteBuffer.allocate(12);
                command2.channel = socket;
                command2.gameServer = gameServer;
                command2.jobs = jobs;
                command2.semaJobs = semaJobs;
                
                //@ semaphore_split(semaJobs);
                //@ semaphore_split(semaJobs);
                
                //@ close SelectAndJoinGameStep2(command, socket);
                //@ close readstringclient(SelectAndJoinGameStep2.class)(command, socket);
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
        catch (IOException ex) {} 
        catch (InterruptedException ex) {}
        
        //@ close thread_run_post(SelectAndJoinGameStep1.class)(this, info);
    }

    public void showGamesHelper(SocketChannel socket, Game game, int count) throws IOException /*@ ensures true; @*/, InterruptedException /*@ ensures true; @*/
    /*@ requires socket != null &*& [?f]channel(socket, ?r) &*& Game(game, count) &*& count >= 0; @*/ 
    /*@ ensures [f]channel(socket, r) &*& Game(game, count); @*/ {
        if (count == 0) {
        } else {
            //@ open Game(game, count);
            String output = game.name + "\r\n";
            byte[] out = output.getBytes();
            ByteBuffer buffer = ByteBuffer.allocate(out.length);
            buffer.put(out);
            buffer.flip();
            socket.write(buffer);
            Game next = game.next;
            //@ open Game(next, count - 1);
            //@ close Game(next, count - 1);
            showGamesHelper(socket, next, count - 1);
            //@ close Game(game, count);
        }
    }
}
