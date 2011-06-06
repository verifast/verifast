package gameserver;

import java.io.*;
import java.nio.*;
import java.nio.channels.*;
import java.util.*;
import java.util.concurrent.*;

/*@
predicate PlayGameStep2(PlayGameStep2 command, SocketChannel socket) = 
    command.playerID |-> ?id &*& 0 < id &*& id < 3
    &*& command.socket |-> socket &*& socket != null
    &*& command.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer)
    &*& command.selector |-> ?selector &*& selector!= null
    &*& command.status |-> ?status &*& status != null 
    &*& command.semaStatus |-> ?semaStatus &*& semaStatus != null &*& gamestatus_ctor_args(?player1, ?player2) &*& semaphore(?f, semaStatus, ?p1, gamestatus_ctor(status, player1, player2))
    &*& command.jobs |-> ?jobs &*& jobs != null
    &*& command.semaJobs |-> ?semaJobs &*& semaJobs != null &*& semaphore(?f2, semaJobs, ?p2, Jobs_ctor(jobs))
    &*& (id == 1 ? socket == player1 : socket == player2);
      
predicate_family_instance readstringclient(PlayGameStep2.class)(PlayGameStep2 client, SocketChannel socket) = 
    PlayGameStep2(client, socket);
    
@*/
public class PlayGameStep2 implements ReadStringClient {
    int playerID;
    SocketChannel socket;
    GameStatus status;
    Semaphore semaStatus;
    Selector selector;
    GameServer gameServer;
    List jobs;
    Semaphore semaJobs;

    public void execute(String line) 
    //@ requires readstringclient(PlayGameStep2.class)(this, ?s) &*& line != null &*& channel(s, 0);
    //@ ensures true;
    {
        //@ open readstringclient(PlayGameStep2.class)(this, s);
        //@ open PlayGameStep2(this, s);
        try {
            GameServer gameServer = this.gameServer;
            //@ open [?f]GameServer(gameServer);

            Executor exec = gameServer.exec;
            List jobs = this.jobs;
            Semaphore semaJobs = this.semaJobs;
            GameStatus status = this.status;
            Semaphore semaStatus = this.semaStatus;

            semaStatus.acquire();
    
            //@ assert gamestatus_ctor_args(?p1, ?p2);
            //@ open gamestatus_ctor(status, p1, p2)();
            //@ open gamestatus(status, p1, p2);
            SocketChannel player1 = status.player1;
            SocketChannel player2 = status.player2;

            int input = -1;
            if (line.matches("[0-2]{1}")) {
                input = Integer.parseInt(line);
            }
            
            //@ close [f]GameServer(gameServer);

            if (input < 0 || input > 2) {
            
                gameServer.writeToSocket("Try again.\r\n", socket);
                
                PlayGameStep2 step2 = new PlayGameStep2();
                step2.gameServer = gameServer;
                step2.status = status;
                step2.semaStatus = semaStatus;
                step2.selector = this.selector;
                step2.jobs = jobs;
                step2.semaJobs = semaJobs;
                step2.playerID = playerID;
                step2.socket = socket;

                ReadString command = new ReadString();
                command.run = step2;
                command.maxCharsToRead = 1;
                command.readSoFar = new String();
                command.buffer = ByteBuffer.allocate(5);
                command.channel = socket;
                command.gameServer = gameServer;
                command.jobs = jobs;
                command.semaJobs = semaJobs;
                
                //@ semaphore_split(semaJobs);
                //@ semaphore_split(semaJobs);
                //@ semaphore_split(semaStatus);
                
                //@ close PlayGameStep2(step2, socket);
                //@ close readstringclient(PlayGameStep2.class)(step2, socket);

                //@ close socket_command(ReadString.class)(command, socket);
                //@ produce_lemma_function_pointer_chunk(ReadString_to_runnable) : socket_command_to_runnable(ReadString.class)() { call(); };

                RegisterSocketJob job = new RegisterSocketJob();
                job.channel = (SelectableChannel) socket;
                job.command = command;
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
            else {                
                if(playerID == 1) {
                    status.player1HasPlayed = true;
                    status.player1Choice = input;
                }
                else {
                    status.player2HasPlayed = true;
                    status.player2Choice = input;
                }
 
                if(status.player1HasPlayed == true && status.player2HasPlayed == true) {
                    gameServer.writeToSocket("\r\nDetermining outcome...\r\n", player1);
                    gameServer.writeToSocket("\r\nDetermining outcome...\r\n", player2);
                    
                    int choice1 = status.player1Choice;
                    int choice2 = status.player2Choice;
                    int ROCK = 0;
                    int PAPER = 1;
                    int SCISSORS = 2;

                    if (choice1 == choice2) {
                        gameServer.writeToSocket("A draw! Try again.\r\n", player1);
                        gameServer.writeToSocket("A draw! Try again.\r\n", player2);

                        status.player1Choice = -1;
                        status.player2Choice = -1;
                        status.player1HasPlayed = false;
                        status.player2HasPlayed = false;

                        // clear remaining input on both channels
                        ByteBuffer buffer = ByteBuffer.allocate(500);
                        player1.read(buffer);
                        buffer.clear();
                        player2.read(buffer);

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
                        
			//@ semaphore_split(semaStatus);
			//@ semaphore_split(semaStatus);
			//@ semaphore_split(semaJobs);
			//@ semaphore_split(semaJobs);
			//@ semaphore_split(semaJobs);
			//@ semaphore_split(semaJobs);
                        
                        //@ close gamestatus_ctor_args(player1, player2);
                        //@ close gamestatus_ctor_args(player1, player2);

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
                    else {
                        status.player1Choice = -1;
                        status.player2Choice = -1;
                        status.player1HasPlayed = false;
                        status.player2HasPlayed = false;

                        if (choice1 == ROCK && choice2 == SCISSORS
                                || choice1 == PAPER && choice2 == ROCK
                                || choice1 == SCISSORS && choice2 == PAPER) {
                            gameServer.writeToSocket("You win.\r\n", player1);
                            gameServer.writeToSocket("You lose.\r\n", player2);
                        }
                        else {
                            gameServer.writeToSocket("You lose.\r\n", player1);
                            gameServer.writeToSocket("You win.\r\n", player2);
                        }
                        //@ open [f]GameServer(gameServer);

                        //@ leak [_]executor(_);

                        DisplayMenu command = new DisplayMenu();
                        command.gameServer = gameServer;
                        command.socket = player1;
                        command.jobs = jobs;
                        command.semaJobs = semaJobs;
                        
                        //@ semaphore_split(semaJobs);

                        //@ close [f]GameServer(gameServer);
                        //@ leak [f/2]GameServer(gameServer);
                        //@ close DisplayMenu(command, player1);
                        //@ close thread_run_pre(DisplayMenu.class)(command, unit);
                        exec.execute(command);

                        command = new DisplayMenu();
                        command.gameServer = gameServer;
                        command.socket = player2;
                        command.jobs = jobs;
                        command.semaJobs = semaJobs;

                        //@ assert [?f2]GameServer(gameServer);
                        //@ leak [f2/2]GameServer(gameServer);
                        //@ close DisplayMenu(command, player2);
                        //@ close thread_run_pre(DisplayMenu.class)(command, unit);
                        exec.execute(command);
                        //@ assert [?f3]GameServer(gameServer);
                        //@ open [f3]GameServer(gameServer);
                    }
                }
                else {
                    gameServer.writeToSocket("\r\nWaiting for other player ...\r\n", socket);
                }
            }
            
            //@ close gamestatus(status, player1, player2);
            //@ close gamestatus_ctor(status, player1, player2)();
            semaStatus.release();
        }
        catch (InterruptedException ex) {}
        catch (IOException ex) {}
    }
}
