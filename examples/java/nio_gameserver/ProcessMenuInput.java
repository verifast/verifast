package gameserver;

import java.io.*;
import java.nio.*;
import java.nio.channels.*;
import java.util.*;
import java.util.concurrent.*;

/*@
predicate ProcessMenuInput(ProcessMenuInput command, SocketChannel socket) = 
    command.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer)  
    &*& command.socket |-> socket &*& socket != null
    &*& command.jobs |-> ?jobs &*& jobs != null
    &*& command.semaJobs |-> ?semaJobs &*& semaJobs != null &*& semaphore(?f, semaJobs, ?p, Jobs_ctor(jobs));

predicate_family_instance readstringclient(ProcessMenuInput.class)(ReadStringClient client, SocketChannel socket) = 
    ProcessMenuInput(^client, socket);

@*/
public class ProcessMenuInput implements ReadStringClient {
    SocketChannel socket;
    GameServer gameServer;
    List jobs;
    Semaphore semaJobs;

    public void execute(String line)
    //@ requires readstringclient(ProcessMenuInput.class)(this, ?s) &*& line != null &*& channel(s, 0);
    //@ ensures true;
    {
        //@ open readstringclient(ProcessMenuInput.class)(this, s);
        //@ open ProcessMenuInput(this, s);
        try {
            GameServer gameServer = this.gameServer;
            //@ open [?f]GameServer(gameServer);
            Executor exec = gameServer.exec;

            SocketChannel socket = this.socket;
            List jobs = this.jobs;
            Semaphore semaJobs = this.semaJobs;
            Selector selector = gameServer.selector;

            int input = -1;
            if (line.matches("[1-6]{1}+")) {
                input = Integer.parseInt(line);
            }
            else {
                //@ close [f]GameServer(gameServer);
                gameServer.writeToSocket("\r\nInvalid choice!\r\n", socket);

                ProcessMenuInput menu = new ProcessMenuInput();
                menu.gameServer = gameServer;
                menu.socket = socket;
                menu.jobs = jobs;
                menu.semaJobs = semaJobs;
                
                //@ semaphore_split(semaJobs);
                
                //@ close ProcessMenuInput(menu, socket);
                //@ close readstringclient(ProcessMenuInput.class)(menu, socket);

                ReadString command = new ReadString();
                command.run = menu;
                command.maxCharsToRead = 1;
                command.readSoFar = new String();
                command.buffer = ByteBuffer.allocate(5);
                command.channel = socket;
                command.gameServer = gameServer;
                command.jobs = jobs;
                command.semaJobs = semaJobs;
                
                //@ semaphore_split(semaJobs);
                               
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

                return;
            }

            //@ close [f]GameServer(gameServer);
            gameServer.writeToSocket("\r\n", socket);
            //@ open [f]GameServer(gameServer);

            if (input == 1) {
                CreateGameStep1 command = new CreateGameStep1();
                command.gameServer = gameServer;
                command.socket = socket;
                command.jobs = jobs;
                command.semaJobs = semaJobs;

                //@ close [f]GameServer(gameServer);
                //@ close CreateGameStep1(command);
                //@ close thread_run_pre(CreateGameStep1.class)(command, unit);
                exec.execute(command);
            }
            else if (input == 2) {
                ShowGames command = new ShowGames();
                command.gameServer = gameServer;
                command.socket = socket;
                command.jobs = jobs;
                command.semaJobs = semaJobs;

                //@ close [f]GameServer(gameServer);
                //@ close ShowGames(command);
                //@ close thread_run_pre(ShowGames.class)(command, unit);
                exec.execute(command);
            }
            else if (input == 3) {
                JoinGame command = new JoinGame();
                command.gameServer = gameServer;
                command.socket = socket;
                command.jobs = jobs;
                command.semaJobs = semaJobs;

                //@ close [f]GameServer(gameServer);
                //@ close JoinGame(command);
                //@ close thread_run_pre(JoinGame.class)(command, unit);
                exec.execute(command);
            }
            else if (input == 4) {
                SelectAndJoinGameStep1 command = new SelectAndJoinGameStep1();
                command.gameServer = gameServer;
                command.socket = socket;
                command.jobs = jobs;
                command.semaJobs = semaJobs;

                //@ close [f]GameServer(gameServer);
                //@ close SelectAndJoinGameStep1(command);
                //@ close thread_run_pre(SelectAndJoinGameStep1.class)(command, unit);
                exec.execute(command);
            }
            else if (input == 5) {
                //@ close [f]GameServer(gameServer);
                gameServer.writeToSocket("Bye!\r\n", socket);
                //@ open [f]GameServer(gameServer);
                
                socket.close();
            }
            else if (input == 6) {
                //@ close [f]GameServer(gameServer);
                gameServer.writeToSocket("Function not supported yet!\r\n", socket);
                //@ open [f]GameServer(gameServer);

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
        }
        catch (InterruptedException ex) {}
        catch (IOException ex) {}
    }
}
