package gameserver;

import java.io.*;
import java.nio.*;
import java.nio.channels.*;
import java.util.*;
import java.util.concurrent.*;

/*@
predicate SelectAndJoinGameStep2(SelectAndJoinGameStep2 command, SocketChannel socket) = 
    command.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer) 
    &*& command.socket |-> socket &*& socket!= null
    &*& command.jobs |-> ?jobs &*& jobs != null
    &*& command.semaJobs |-> ?semaJobs &*& semaJobs != null &*& semaphore(?f, semaJobs, ?p, Jobs_ctor(jobs));
    
predicate_family_instance readstringclient(SelectAndJoinGameStep2.class)(SelectAndJoinGameStep2 client, SocketChannel socket) = 
    SelectAndJoinGameStep2(client, socket);

@*/
public class SelectAndJoinGameStep2 implements ReadStringClient {
    SocketChannel socket;
    GameServer gameServer;
    List jobs;
    Semaphore semaJobs;

    public void execute(String line)
    //@ requires readstringclient(SelectAndJoinGameStep2.class)(this, ?s) &*& line != null &*& channel(s, 0);
    //@ ensures true;
    {
        //@ open readstringclient(SelectAndJoinGameStep2.class)(this, s);
        //@ open SelectAndJoinGameStep2(this, s);
        try {
            GameServer gameServer = this.gameServer;
            //@ open [?f]GameServer(gameServer);

            Semaphore semaGames = gameServer.semaGames;
            Games games = gameServer.games;
            SocketChannel socket = this.socket;
            Selector selector = gameServer.selector;
	    
	    //@ semaphore_simple_split(semaGames);
            semaGames.acquire();
            //@ open Games_ctor(games)();
            //@ open Games(games);

            int input = 1;
            if (line.matches("[0-9]+")) {
                input = Integer.parseInt(line);
            } 
            else {
                input = -1;
            }

            if (input < 1 || input > games.count) {
                //@ close [f]GameServer(gameServer);
                gameServer.writeToSocket("\r\nInvalid choice. Try again.\r\n", socket);
                
                SelectAndJoinGameStep2 step2 = new SelectAndJoinGameStep2();
                step2.gameServer = gameServer;
                step2.socket = socket;
                step2.jobs = jobs;
                step2.semaJobs = semaJobs;

                ReadString command = new ReadString();
                command.run = step2;
                command.maxCharsToRead = 12;
                command.readSoFar = new String();
                command.buffer = ByteBuffer.allocate(12);
                command.channel = socket;
                command.gameServer = gameServer;
                command.jobs = jobs;
                command.semaJobs = semaJobs;
                
                //@ semaphore_split(semaJobs);
                //@ semaphore_split(semaJobs);

                //@ close SelectAndJoinGameStep2(step2, socket);
                //@ close readstringclient(SelectAndJoinGameStep2.class)(step2, socket);

                //@ close socket_command(ReadString.class)(command, socket);
                //@ produce_lemma_function_pointer_chunk(ReadString_to_runnable) : socket_command_to_runnable(ReadString.class)() { call(); };

                //@ close Games(games);
                //@ close Games_ctor(games)();
                semaGames.release();

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
            Game joinedGame;
            if (input == 1) {
                joinedGame = games.head;
                //@ open Game(joinedGame, ?c);
                games.head = joinedGame.next;
            }
            else {
                joinedGame = selectGameHelper(games.head, input-1);
            }
            games.count = games.count - 1;
            Game head = games.head;
            //@ close Games(games);
            //@ close Games_ctor(games)();
            semaGames.release();
            
            //@ close [f]GameServer(gameServer);
            gameServer.joinGameCore(socket, semaGames, games, joinedGame, jobs, semaJobs);
        } 
        catch (IOException ex) {}
        catch (InterruptedException ex) {}
    }

    public Game selectGameHelper(Game game, int choice) 
    //@ requires Game(game, ?count) &*& choice < count &*& 1 <= choice;
    /*@ ensures Game(game, count - 1) &*& result.name |-> ?name &*& result.socket |-> ?socket &*& socket != null 
        &*& channel(socket, 0) &*& result.next |-> ?next; @*/ 
    {
        Game joinedGame;
        //@ open Game(game, count);
        if (choice == 1) {
            joinedGame = game.next;
            //@ open Game(joinedGame, ?c);
            game.next = joinedGame.next;
        } 
        else {
            joinedGame = selectGameHelper(game.next, choice - 1);
        }
        //@ close Game(game, count - 1);

        return joinedGame;
    }
}
