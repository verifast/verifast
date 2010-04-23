package chat;

import java.io.*;
import java.net.*;
import java.util.*;
import java.util.concurrent.*;

/*@

predicate_ctor room_ctor(Room room)() = room(room);

predicate session(Session session) =
    session.room |-> ?room &*& session.room_lock |-> ?roomLock &*& session.socket |-> ?socket &*& socket != null &*& Socket(socket, ?in, ?inInfo, ?out, ?outInfo)
    &*& roomLock != null &*& [?f]lock(roomLock, room_ctor(room)) &*& InputStream(in.getClass())(in, inInfo) &*& OutputStream(out.getClass())(out, outInfo);

predicate_family_instance thread_run_pre(Session.class)(Session session, any info) = session(session);

predicate_family_instance thread_run_post(Session.class)(Session session, any info) = true;

@*/

public class Session implements Runnable {
    Room room;
    Semaphore room_lock;
    Socket socket;
    
    public Session(Room room, Semaphore roomLock, Socket socket)
        /*@
        requires
            roomLock != null &*& [?f]lock(roomLock, room_ctor(room)) &*&
            socket != null &*& Socket(socket, ?in, ?inInfo, ?out, ?outInfo) &*& InputStream(in.getClass())(in, inInfo) &*& OutputStream(out.getClass())(out, outInfo);
        @*/
        //@ ensures session(this);
    {
        this.room = room;
        this.room_lock = roomLock;
        this.socket = socket;
        //@ close session(this);
    }
    
    public void run_with_nick(Room room, Semaphore roomLock, BufferedReader reader, Writer writer, String nick) throws InterruptedException, IOException
        /*@
        requires
            roomLock != null &*& locked(roomLock, room_ctor(room), ?f) &*& room!= null &*& room(room) &*&
            reader != null &*& BufferedReader(reader, ?reader0, ?reader0Info) &*&
            writer != null &*& Writer(writer.getClass())(writer, ?writerInfo);
        @*/
        //@ ensures [f]lock(roomLock, room_ctor(room)) &*& BufferedReader(reader, reader0, reader0Info) &*& Writer(writer.getClass())(writer, writerInfo);
    {
        Member member = null;
        String joinMessage = nick + " has joined the room.";
        room.broadcast_message(joinMessage);
        {
            //@ open room(room);
            member = new Member(nick, writer);
            List list = room.members;
            list.add(member);
            //@ open foreach<Member>(?members, @member);
            //@ close foreach(members, @member);
            //@ foreach_member_not_contains(members, member);
            //@ close foreach<Member>(nil, @member);
            //@ close foreach<Member>(cons<Member>(member, nil), @member);
            //@ foreach_append<Member>(members, cons<Member>(member, nil));
            //@ close room(room);
        }
        //@ close room_ctor(room)();
        roomLock.release();
        
        {
            String message = reader.readLine();
            while (message != null)
                //@ invariant BufferedReader(reader, reader0, reader0Info) &*& [f]lock(roomLock, room_ctor(room));
            {
                roomLock.acquire();
                //@ open room_ctor(room)();
                room.broadcast_message(nick + " says: " + message);
                //@ close room_ctor(room)();
                roomLock.release();
                message = reader.readLine();
            }
        }
        
        roomLock.acquire();
        //@ open room_ctor(room)();
        //@ open room(room);
        {
            List membersList = room.members;
            //@ assert foreach<Member>(?members, @member);
            //@ assume(mem<Member>(member, members));
            membersList.remove(member);
            //@ foreach_remove<Member>(member, members);
        }
        //@ close room(room);
        {
            room.broadcast_message(nick + " left the room.");
        }
        //@ close room_ctor(room)();
        roomLock.release();
        
        //@ open member(member);
        //@ assert Writer(?memberWriterClass)(?memberWriter, ?memberWriterInfo);
        //@ assume(memberWriterClass == memberWriter.getClass() && memberWriter == writer && memberWriterInfo == writerInfo);
    }
    
    public void run()
        //@ requires thread_run_pre(Session.class)(this, ?info);
        //@ ensures thread_run_post(Session.class)(this, info);
    {
        try {
            this.runCore();
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
    
    public void runCore() throws InterruptedException, IOException
        //@ requires thread_run_pre(Session.class)(this, ?info);
        //@ ensures thread_run_post(Session.class)(this, info);
    {
        //@ open thread_run_pre(Session.class)(this,info);
        //@ open session(this);
        Room room = this.room;
        Semaphore roomLock = this.room_lock;
        Socket socket = this.socket;
        InputStream in = socket.getInputStream();
        //@ assert InputStream(in.getClass())(in, ?inInfo);
        InputStreamReader reader0 = new InputStreamReader(in);
        //@ InputStreamReader_upcast(reader0);
        BufferedReader reader = new BufferedReader(reader0);
        //@ assert BufferedReader(reader, reader0, ?readerInfo);
        OutputStream out = socket.getOutputStream();
        //@ assert OutputStream(out.getClass())(out, ?outInfo);
        OutputStreamWriter writer0 = new OutputStreamWriter(out);
        //@ OutputStreamWriter_upcast(writer0);
        BufferedWriter writer1 = new BufferedWriter(writer0);
        //@ BufferedWriter_upcast(writer1);
        Writer writer = writer1;
        //@ assert Writer(writer.getClass())(writer, ?writerInfo);
        
        writer.write("Welcome to the chat room.\r\n");
        writer.write("The following members are present: ");
        
        roomLock.acquire();
        //@ open room_ctor(room)();
        //@ open room(room);
        {
            List membersList = room.members;
            //@ assert foreach<Member>(?members, @member);
            Iterator iter = membersList.iterator();
            boolean hasNext = iter.hasNext();
            //@ length_nonnegative(members);
            while (hasNext)
                /*@
                invariant
                    Writer(writer.getClass())(writer, writerInfo) &*&
                    iter(iter, membersList, members, ?i) &*& foreach(members, @member)
                    &*& hasNext == (i < length(members)) &*& 0 <= i &*& i <= length(members);
                @*/
            {
                Object o = iter.next();
                Member member = (Member)o;
                //@ mem_nth(i, members);
                //@ foreach_remove<Member>(member, members);
                //@ open member(member);
                writer.write(member.nick);
                writer.write("  ");
                //@ close member(member);
                //@ foreach_unremove<Member>(member, members);
                hasNext = iter.hasNext();
            }
            writer.write("\r\n");
            writer.flush();
            //@ iter_dispose(iter);
        }
        //@ close room(room);
        //@ close room_ctor(room)();
        roomLock.release();

        {
            boolean done = false;
            while (!done)
                //@ invariant Writer(writer.getClass())(writer, writerInfo) &*& BufferedReader(reader, reader0, readerInfo) &*& [?f]lock(roomLock, room_ctor(room));
            {
                writer.write("Please enter your nick: \r\n");
                writer.flush();
                {
                    String nick = reader.readLine();
                    if (nick == null) {
                        done = true;
                    } else {
                        roomLock.acquire();
                        //@ open room_ctor(room)();
                        {
                            if (room.has_member(nick)) {
                                //@ close room_ctor(room)();
                                roomLock.release();
                                writer.write("Error: This nick is already in use.\r\n");
                                writer.flush();
                            } else {
                                this.run_with_nick(room, roomLock, reader, writer, nick);
                                done = true;
                            }
                        }
                    }
                }
            }
        }
        
        //@ BufferedReader_dispose(reader);
        //@ InputStreamReader_downcast(reader0, in, inInfo);
        //@ InputStreamReader_dispose(reader0);
        //@ BufferedWriter_downcast(writer1, writer0, OutputStreamWriter_info(out, outInfo));
        //@ BufferedWriter_dispose(writer1);
        //@ OutputStreamWriter_downcast(writer0, out, outInfo);
        //@ OutputStreamWriter_dispose(writer0);
        socket.close();
        //@ close thread_run_post(Session.class)(this,info);
    }
}