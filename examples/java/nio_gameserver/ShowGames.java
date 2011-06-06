package gameserver;

import java.io.*;
import java.nio.*;
import java.nio.channels.*;
import java.util.*;
import java.util.concurrent.*;

/*@
predicate ShowGames(ShowGames command) = 
    command.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer) 
    &*& command.socket |-> ?socket &*& socket!= null &*& channel(socket, 0)
    &*& command.jobs |-> ?jobs &*& jobs != null
    &*& command.semaJobs |-> ?semaJobs &*& semaJobs != null &*& semaphore(?f, semaJobs, ?p, Jobs_ctor(jobs));

predicate_family_instance thread_run_pre(ShowGames.class)(ShowGames run, any info) = 
    ShowGames(run);
predicate_family_instance thread_run_post(ShowGames.class)(ShowGames run, any info) = 
    true;
@*/
public class ShowGames implements Runnable {
    SocketChannel socket;
    GameServer gameServer;
    List jobs;
    Semaphore semaJobs;

    public void run()
    //@ requires thread_run_pre(ShowGames.class)(this, ?info);
    //@ ensures thread_run_post(ShowGames.class)(this, info);
    {
        //@ open thread_run_pre(ShowGames.class)(this, info);
        //@ open ShowGames(this);
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
            //@ close [f]GameServer(gameServer);
            gameServer.writeToSocket("There are " + String.valueOf(games.count) + " available games:\r\n", socket);
            //@ open [f]GameServer(gameServer);

            //@ close [f]GameServer(gameServer);
            showGamesHelper(socket, games.head, games.count);
            
            //@ close Games(games);
            //@ close Games_ctor(games)();
            semaGames.release();

            DisplayMenu command = new DisplayMenu();
            command.gameServer = gameServer;
            command.socket = socket;
            command.jobs = jobs;
            command.semaJobs = semaJobs;

            //@ close DisplayMenu(command, socket);
            //@ close thread_run_pre(DisplayMenu.class)(command, unit);

            exec.execute(command);
        } catch (IOException ex) {} 
        catch (InterruptedException ex) {}
        
        //@ close thread_run_post(ShowGames.class)(this, info);
    }

    public void showGamesHelper(SocketChannel socket, Game game, int count) throws IOException /*@ ensures true; @*/, InterruptedException /*@ ensures true; @*/
    /*@ requires socket != null &*& channel(socket, 0) &*& Game(game, count) &*& count >= 0 &*& [?f2]this.gameServer |-> ?gs &*& gs != null &*& [?f3]GameServer(gs); @*/ 
    /*@ ensures channel(socket, 0) &*& Game(game, count) &*& [f2]this.gameServer |-> gs &*& [f3]GameServer(gs); @*/ {
        if (count == 0) {
        } else {
            //@ open Game(game, count);            
            GameServer gameServer = this.gameServer;
            gameServer.writeToSocket(game.name + "\r\n", socket);
            Game next = game.next;
            //@ open Game(next, count - 1);
            //@ close Game(next, count - 1);
            showGamesHelper(socket, next, count - 1);
            //@ close Game(game, count);
        }
    }
}
