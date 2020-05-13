package chat;

import java.io.*;
import java.util.*;

/*@

predicate room(Room room) =
    room.members |-> ?membersList &*& membersList != null &*& foreach<Member>(?members, member) &*& membersList.List(members);

@*/

public class Room {
    List members;

    public Room()
        //@ requires emp;
        //@ ensures room(this);
    {
        List a = new ArrayList();
        this.members = a;
        //@ close foreach<Member>(nil, member);
        //@ close room(this);
    }
    
    public boolean has_member(String nick)
        //@ requires room(this) &*& nick != null;
        //@ ensures room(this);
    {
        //@ open room(this);
        //@ assert foreach(?members, _);
        List membersList = this.members;
        //@ membersList.listToIterable();
        Iterator iter = membersList.iterator();
        boolean hasMember = false;
        boolean hasNext = iter.hasNext();
        while (hasNext && !hasMember)
            /*@
            invariant
                iter.Iterator((seq_of_list)(members), _, ?i) &*& Iterable_iterating(membersList.getClass())(membersList, members, 1, iter) &*& foreach(members, @member)
                &*& hasNext == (i < length(members)) &*& 0 <= i &*& i <= length(members);
            @*/
        {
            Member member = (Member) iter.next();
            //@ foreach_remove<Member>(member, members);
            //@ open member(member);
            hasMember = nick.equals(member.nick);
            //@ close member(member);
            //@ foreach_unremove<Member>(member, members);
            hasNext = iter.hasNext();
        }
        //@ membersList.destroyIterator();
        //@ membersList.iterableToList();
        //@ close room(this);
        return hasMember;
    }
    
    public void broadcast_message(String message) throws IOException /*@ ensures true; @*/
        //@ requires room(this) &*& message != null;
        //@ ensures room(this);
    {
        //@ open room(this);
        //@ assert foreach(?members0, _);
        List membersList = this.members;
        //@ membersList.listToIterable();
        Iterator iter = membersList.iterator();
        boolean hasNext = iter.hasNext();
        //@ length_nonnegative(members0);
        while (hasNext)
            /*@
            invariant
                foreach<Member>(?members, @member) &*& iter.Iterator((seq_of_list)(members), _, ?i) &*& Iterable_iterating(membersList.getClass())(membersList, members, 1, iter)
                &*& hasNext == (i < length(members)) &*& 0 <= i &*& i <= length(members);
            @*/
        {
            Member member = (Member) iter.next();
            //@ mem_nth(i, members);
            //@ foreach_remove<Member>(member, members);
            //@ open member(member);
            Writer writer = member.writer;
            writer.write(message);
            writer.write("\r\n");
            writer.flush();
            //@ close member(member);
            //@ foreach_unremove<Member>(member, members);
            hasNext = iter.hasNext();
        }
        //@ membersList.destroyIterator();
        //@ membersList.iterableToList();
        //@ close room(this);
    }
}