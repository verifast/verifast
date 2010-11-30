package gameserver;

import java.io.*;
import java.util.concurrent.*;

/*@
predicate StartSession(StartSession session) = 
        session.gameServer |-> ?gameServer &*& gameServer != null &*& session.socket |-> ?socket &*& socket!= null
        &*& bufferedsocket(socket, ?reader, ?writer) &*& session.games |-> ?games &*& games != null
        &*& session.semaphore |-> ?semaphore &*& semaphore != null &*& semaphore(?f, semaphore, ?p, Games_ctor(games));

predicate_family_instance thread_run_pre(StartSession.class)(StartSession run, any info) = 
        StartSession(run);
predicate_family_instance thread_run_post(StartSession.class)(StartSession run, any info) = 
        true;
@*/

public class StartSession implements Runnable {
    GameServer gameServer;
    BufferedSocket socket;
    Games games;
    Semaphore semaphore;

    public void run()
    //@ requires thread_run_pre(StartSession.class)(this, ?info);
    //@ ensures thread_run_post(StartSession.class)(this, info);
    {
        //@ open thread_run_pre(StartSession.class)(this, info);
        //@ open StartSession(this);
        try {
            gameServer.mainMenu(socket, semaphore, games);
        } 
        catch (IOException ex) {}
        catch (InterruptedException ex) {}
        //@ close thread_run_post(StartSession.class)(this, info);
    }
}
