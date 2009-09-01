package chat;

import java.util.*;
import wrapper.io.*;

/*@

predicate room(Room room) =
    room.members |-> ?membersList &*& list(membersList, ?members) &*& foreach(members, member);

@*/

public class Room {
    List members;

    public Room()
        //@ requires emp;
        //@ ensures room(result);
    {
        List a = new ArrayList();
        this.members = a;
        //@ close foreach(nil, member);
        //@ close room(this);
    }
    
    public boolean has_member(String nick)
        //@ requires room(this);
        //@ ensures room(this);
    {
        //@ open room(this);
        //@ assert foreach(?members, _);
        List membersList = this.members;
        Iterator iter = membersList.iterator();
        boolean hasMember = false;
        boolean hasNext = iter.hasNext();
        //@ lengthPositive(members);
        while (hasNext && !hasMember)
            /*@
            invariant
                iter(iter, membersList, members, ?i) &*& foreach(members, @member)
                &*& hasNext == (i < length(members)) &*& 0 <= i &*& i <= length(members);
            @*/
        {
            Object o = iter.next();
            Member member = (Member)o;
            //@ containsIth(members, i);
            //@ foreach_remove(members, member);
            //@ open member(member);
            hasMember = nick.equals(member.nick);
            //@ close member(member);
            //@ foreach_unremove(members, member);
            hasNext = iter.hasNext();
        }
        //@ iter_dispose(iter);
        //@ close room(this);
        return hasMember;
    }
    
    public void broadcast_message(String message)
        //@ requires room(this);
        //@ ensures room(this);
    {
        //@ open room(this);
        //@ assert foreach(?members0, _);
        List membersList = this.members;
        Iterator iter = membersList.iterator();
        boolean hasNext = iter.hasNext();
        //@ lengthPositive(members0);
        while (hasNext)
            /*@
            invariant
                iter(iter, membersList, ?members, ?i) &*& foreach(members, @member)
                &*& hasNext == (i < length(members)) &*& 0 <= i &*& i <= length(members);
            @*/
        {
            Object o = iter.next();
            Member member = (Member)o;
            //@ containsIth(members, i);
            //@ foreach_remove(members, member);
            //@ open member(member);
            OutputStreamWriter_ writer = member.writer;
            writer.write(message);
            writer.write("\r\n");
            //@ close member(member);
            //@ foreach_unremove(members, member);
            hasNext = iter.hasNext();
        }
        //@ iter_dispose(iter);
        //@ close room(this);
    }
}