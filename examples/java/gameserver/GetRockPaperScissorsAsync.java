package gameserver;

import java.io.*;
import java.util.concurrent.*;

/*@
predicate GetRockPaperScissorsAsync(GetRockPaperScissorsAsync rps, BufferedReader r, BufferedWriter w) = 
        rps.gameServer |-> ?gameServer &*& gameServer != null &*& rps.session |-> ?session &*& session!= null &*& RPSSession(session, r, w)
        &*& rps.semaphore_ |-> ?semaphore &*& semaphore != null &*& semaphore(?f, semaphore, ?p, Session_ctor(session, r, w));

predicate_family_instance thread_run_pre(GetRockPaperScissorsAsync.class)(GetRockPaperScissorsAsync run, set<BufferedReader, BufferedWriter> rw) = 
        GetRockPaperScissorsAsync(run, fst(rw), snd(rw));
predicate_family_instance thread_run_post(GetRockPaperScissorsAsync.class)(GetRockPaperScissorsAsync run, any info) = 
        true;
@*/

public class GetRockPaperScissorsAsync implements Runnable {
    GameServer gameServer;
    RPSSession session;
    Semaphore semaphore_;

    public void run()
    //@ requires thread_run_pre(GetRockPaperScissorsAsync.class)(this, ?info);
    //@ ensures thread_run_post(GetRockPaperScissorsAsync.class)(this, info);
    {
        //@ open thread_run_pre(GetRockPaperScissorsAsync.class)(this, ?info2);
        try {
            //@ open GetRockPaperScissorsAsync(this, fst(info2), snd(info2));
            gameServer.getRPS(session);
            //@ close Session_ctor(session, fst(info2), snd(info2))();
            semaphore_.release();
        }
        catch (IOException ex) {}
        //@ close thread_run_post(GetRockPaperScissorsAsync.class)(this, info);
    }
}
