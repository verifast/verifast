package chat;

import java.io.*;
import java.net.*;
import java.util.*;
import java.util.concurrent.*;

class ListUtil {
    
    static <T> void remove(List<T> l, T o) // Like l.remove(o), except uses identity comparison instead of .equals().
        //@ requires l.List(?es);
        //@ ensures l.List(remove(o, es));
    {
        for (int i = 0; i < l.size(); i++)
            //@ invariant l.List(es) &*& 0 <= i &*& i <= index_of(o, es);
        {
            if (l.get(i) == o) {
                l.remove(i);
                //@ remove_remove_nth(o, es);
                //@ index_of_nth(i, es);
                break;
            }
            //@ if (index_of(o, es) == i) { nth_index_of(o, es); }
        }
        //@ if (mem(o, es)) { mem_index_of(o, es); } else { mem_remove_eq(o, es); }
    }
    
}

/*@

predicate_ctor room_ctor(Room room)() = room(room);

predicate session(Session session;) =
    session.room |-> ?room &*& session.room_lock |-> ?roomLock &*& session.socket |-> ?socket &*& socket != null &*& socket.Socket(?i, ?o)
    &*& roomLock != null &*& [_]roomLock.Semaphore(room_ctor(room)) &*& i.InputStream() &*& o.OutputStream();

@*/

public final class Session implements Runnable {
    Room room;
    Semaphore room_lock;
    Socket socket;
    
    //@ predicate pre() = session(this);
    //@ predicate post() = true;
    
    public Session(Room room, Semaphore roomLock, Socket socket)
        /*@
        requires
            roomLock != null &*& [_]roomLock.Semaphore(room_ctor(room)) &*&
            socket != null &*& socket.Socket(?i, ?o) &*& i.InputStream() &*& o.OutputStream();
        @*/
        //@ ensures session(this);
    {
        this.room = room;
        this.room_lock = roomLock;
        this.socket = socket;
        //@ close session(this);
    }
    
    public void run_with_nick(Room room, Semaphore roomLock, BufferedReader reader, Writer writer, String nick) throws InterruptedException /*@ ensures true; @*/, IOException /*@ ensures true; @*/
        /*@
        requires
            roomLock != null &*& [_]roomLock.Semaphore(room_ctor(room)) &*& room != null &*& room(room) &*&
            reader != null &*& reader.Reader() &*&
            writer != null &*& writer.Writer();
        @*/
        //@ ensures [_]roomLock.Semaphore(room_ctor(room)) &*& reader.Reader() &*& writer.Writer();
    {
        Member member = null;
        String joinMessage = nick + " has joined the room.";
        room.broadcast_message(joinMessage);
        {
            //@ open room(room);
            member = new Member(nick, writer);
            List<Member> list = room.members;
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
        //@ roomLock.makeHandle();
        roomLock.release();
        
        {
            String message = reader.readLine();
            while (message != null)
                //@ invariant reader.Reader() &*& [_]roomLock.Semaphore(room_ctor(room));
            {
                //@ roomLock.makeHandle();
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
            List<Member> membersList = room.members;
            //@ assert foreach<Member>(?members, @member);
            //@ assume(mem<Member>(member, members)); // TODO: Eliminate using a ghost list.
            ListUtil.remove(membersList, member);
            //@ foreach_remove<Member>(member, members);
        }
        //@ close room(room);
        {
            room.broadcast_message(nick + " left the room.");
        }
        //@ close room_ctor(room)();
        roomLock.release();
        
        //@ open member(member);
    }
    
    public void run()
        //@ requires pre();
        //@ ensures post();
    {
        try {
            this.runCore();
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
    
    public void runCore() throws InterruptedException /*@ ensures true; @*/, IOException /*@ ensures true; @*/
        //@ requires pre();
        //@ ensures post();
    {
        //@ open pre();
        //@ open session(this);
        Room room = this.room;
        Semaphore roomLock = this.room_lock;
        Socket socket = this.socket;
        InputStream in = socket.getInputStream();
        InputStreamReader reader0 = new InputStreamReader(in);
        BufferedReader reader = new BufferedReader(reader0);
        OutputStream out = socket.getOutputStream();
        OutputStreamWriter writer0 = new OutputStreamWriter(out);
        BufferedWriter writer1 = new BufferedWriter(writer0);
        Writer writer = writer1;
        
        writer.write("Welcome to the chat room.\r\n");
        writer.write("The following members are present: ");
        
        //@ roomLock.makeHandle();
        roomLock.acquire();
        //@ open room_ctor(room)();
        //@ open room(room);
        {
            List<Member> membersList = room.members;
            //@ assert foreach<Member>(?members, @member);
            //@ membersList.listToIterable();
            Iterator<Member> iter = membersList.iterator();
            boolean hasNext = iter.hasNext();
            while (hasNext)
                /*@
                invariant
                    writer.Writer() &*&
                    iter.Iterator((seq_of_list)(members), _, ?i) &*& Iterable_iterating(membersList.getClass())(membersList, members, 1, iter)
                    &*& foreach(members, @member) &*& hasNext == (i < length(members)) &*& 0 <= i &*& i <= length(members);
                @*/
            {
                Member member = iter.next();
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
            //@ membersList.destroyIterator();
            //@ membersList.iterableToList();
        }
        
        //@ close room(room);
        //@ close room_ctor(room)();
        roomLock.release();

        {
            boolean done = false;
            while (!done)
                //@ invariant writer.Writer() &*& reader.Reader() &*& [_]roomLock.Semaphore(room_ctor(room));
            {
                writer.write("Please enter your nick: \r\n");
                writer.flush();
                {
                    String nick = reader.readLine();
                    if (nick == null) {
                        done = true;
                    } else {
                        //@ roomLock.makeHandle();
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
        
        //@ reader.destroy();
        //@ reader0.destroy();
        //@ writer1.destroy();
        //@ writer0.destroy();
        socket.close();
        //@ close post();
    }
}