package gameserver;

import java.io.*;
import java.nio.*;
import java.nio.channels.*;
import java.util.*;
import java.util.concurrent.*;

/*@
predicate_family_instance socket_command(ReadString.class)(ReadString command, SocketChannel channel) = 
    command.channel |-> channel &*& channel != null
    &*& command.run |-> ?run &*& run != null &*& readstringclient(run.getClass())(run, channel)
    &*& command.buffer |-> ?buffer &*& buffer != null &*& bytebuffer(buffer, ?cap, ?lim, ?pos)
    &*& command.maxCharsToRead |-> ?maxCharsToRead &*& 0 < maxCharsToRead
    &*& command.readSoFar |-> ?readSoFar &*& readSoFar != null
    &*& command.line |-> ?line
    &*& command.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer)
    &*& command.jobs |-> ?jobs &*& jobs != null
    &*& command.semaJobs |-> ?semaJobs &*& semaJobs != null &*& semaphore(?f, semaJobs, ?p, Jobs_ctor(jobs));

predicate_family_instance thread_run_pre(ReadString.class)(ReadString run, any info) = 
    run.channel |-> ?channel &*& channel != null &*& channel(channel, 0)
    &*& run.run |-> ?r &*& r != null &*& readstringclient(r.getClass())(r, channel)
    &*& run.buffer |-> ?buffer &*& buffer != null &*& bytebuffer(buffer, ?cap, ?lim, ?pos)
    &*& run.maxCharsToRead |-> ?maxCharsToRead &*& 0 < maxCharsToRead
    &*& run.readSoFar |-> ?readSoFar &*& readSoFar != null
    &*& run.line |-> ?line
    &*& run.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer)
    &*& run.jobs |-> ?jobs &*& jobs != null
    &*& run.semaJobs |-> ?semaJobs &*& semaJobs != null &*& semaphore(?f, semaJobs, ?p, Jobs_ctor(jobs));
    
predicate_family_instance thread_run_post(ReadString.class)(ReadString run, any info) = 
    true;

lemma void ReadString_to_runnable()
    requires socket_command(ReadString.class)(?command, ?channel) &*& channel(channel, 0);
    ensures thread_run_pre(ReadString.class)(command, _);
{
    open socket_command(ReadString.class)(?command_, ?channel_);
    close thread_run_pre(ReadString.class)(command_, unit);
}

@*/

public class ReadString implements Runnable {
    ReadStringClient run;
    int maxCharsToRead;
    String readSoFar;
    String line;
    ByteBuffer buffer;
    SocketChannel channel;
    GameServer gameServer;
    List jobs;
    Semaphore semaJobs;

    public void run() 
    //@ requires thread_run_pre(ReadString.class)(this, ?info);
    //@ ensures thread_run_post(ReadString.class)(this, info);
    {
        try {
            //@ open thread_run_pre(ReadString.class)(this, info);
            ReadStringClient run = this.run;
            int maxCharsToRead = this.maxCharsToRead;
            String readSoFar = this.readSoFar;
            ByteBuffer buffer = this.buffer;
            SocketChannel channel = this.channel;
            GameServer gameServer = this.gameServer;
            List jobs = this.jobs;
            Semaphore semaJobs = this.semaJobs;
            //@ open GameServer(gameServer);
            Selector selector = gameServer.selector;
            
            buffer.clear();
            int charsRead = channel.read(buffer);
            buffer.flip();
            int remaining = buffer.remaining();
            byte[] r = new byte[remaining];
            buffer.get(r);
            maxCharsToRead = maxCharsToRead - charsRead;
            
            if(charsRead > 0) {
		    byte[] t = new byte[buffer.position()-1];
		    System.arraycopy(r, 0, t, 0, buffer.position()-1);
		    readSoFar = readSoFar + new String(t);
            }

            byte[] dest = new byte[buffer.position()];
            System.arraycopy(r, 0, dest, 0, buffer.position());
                        
            boolean containsNL = false;
            if(dest.length > 0) {
                containsNL = dest[dest.length-1] == 10 || dest[dest.length-1] == 13;
            }

            if(charsRead == -1 && !containsNL && maxCharsToRead > 0) {
                channel.close();
            }
            else if (!containsNL && maxCharsToRead > 0) {
                ReadString command = new ReadString();
                command.run = run;
                command.maxCharsToRead = maxCharsToRead;
                command.readSoFar = readSoFar;
                command.buffer = buffer;
                command.channel = channel;
                command.gameServer = gameServer;
                command.jobs = jobs;
                command.semaJobs = semaJobs;
                
                //@ semaphore_split(semaJobs);

                //@ close socket_command(ReadString.class)(command, channel);
                //@ produce_lemma_function_pointer_chunk(ReadString_to_runnable) : socket_command_to_runnable(ReadString.class)() { call(); };

                RegisterSocketJob job = new RegisterSocketJob();
                job.channel = (SelectableChannel) channel;
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
                readSoFar = readSoFar.trim();
                line = readSoFar;
                buffer.clear();
                
                run.execute(line);
            }
        }
        catch (InterruptedException ex) {}
        catch (IOException ex) {}
        
        //@ close thread_run_post(ReadString.class)(this, info);
    }
}
