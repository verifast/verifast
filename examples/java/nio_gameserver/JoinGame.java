package gameserver;

import java.io.*;
import java.nio.*;
import java.nio.channels.*;
import java.util.*;
import java.util.concurrent.*;

/*@
predicate JoinGame(JoinGame command) = 
    command.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer)  
    &*& command.socket |-> ?socket &*& socket!= null &*& channel(socket, 0)
    &*& command.jobs |-> ?jobs &*& jobs != null
    &*& command.semaJobs |-> ?semaJobs &*& semaJobs != null &*& semaphore(?f, semaJobs, ?p, Jobs_ctor(jobs));

predicate_family_instance thread_run_pre(JoinGame.class)(JoinGame run, any info) = 
    JoinGame(run);
predicate_family_instance thread_run_post(JoinGame.class)(JoinGame run, any info) = 
    true;
@*/
public class JoinGame implements Runnable {
    SocketChannel socket;
    GameServer gameServer;
    List jobs;
    Semaphore semaJobs;
    
    public void run() 
    //@ requires thread_run_pre(JoinGame.class)(this, ?info);
    //@ ensures thread_run_post(JoinGame.class)(this, info);
    {
        //@ open thread_run_pre(JoinGame.class)(this, info);
        //@ open JoinGame(this);
        try {
            GameServer gameServer = this.gameServer;
            //@ open [?f]GameServer(gameServer);
            Executor exec = gameServer.exec;
            Semaphore semaGames = gameServer.semaGames;
            Games games = gameServer.games;
            
            //@ semaphore_simple_split(semaGames);

            semaGames.acquire();
            //@ open Games_ctor(games)();
            //@ open Games(games);
            if (games.count == 0) {
                //@ close [f]GameServer(gameServer);
                gameServer.writeToSocket("\r\nNo game is available.\r\n", socket);
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
                Game joinedGame = games.head;
                //@ open Game(joinedGame, ?count);
                games.head = joinedGame.next;
                games.count = games.count - 1;
                Game head = games.head;
                int gamesCount = games.count;
                //@ open Game(head, gamesCount);
                //@ close Game(head, gamesCount);
                //@ close Games(games);
                //@ close Games_ctor(games)();
                semaGames.release();

                //@ close [f]GameServer(gameServer);
                gameServer.joinGameCore(socket, semaGames, games, joinedGame, jobs, semaJobs);
            }
        } 
        catch (InterruptedException ex) {
            
        } 
        catch (IOException ex) {

        }
        //@ close thread_run_post(JoinGame.class)(this, info);
    }
}
