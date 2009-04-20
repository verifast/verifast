package chat;

import java.util.*;
import wrapper.io.*;
public class Room{
  List members;
  public Room()
    //@ requires emp;
    //@ ensures room(result);
  {
    List a=new ArrayList();
    this.members = a;
    //@ close foreach(nil, member);
    //@ close room(this);
  }
  public boolean has_member(StringBuffer nick)
    //@ requires room(this) &*& string_buffer(nick);
    //@ ensures room(this) &*& string_buffer(nick);
{
    //@ open room(this);
    //@ assert foreach(?members, _);
    List membersList = this.members;
    Iterator iter = membersList.iterator();
    boolean hasMember = false;
    boolean hasNext = iter.hasNext();
    //@ lengthPositive(members);
    while (hasNext && !hasMember)
        //@ invariant string_buffer(nick) &*& iter(iter, membersList, members, ?i) &*& foreach(members, @member) &*& hasNext == (i < length(members)) &*& 0 <= i &*& i <= length(members);
    {
        Object o=iter.next();
        Member member = (Member)o;
        //@ containsIth(members, i);
        //@ foreach_remove(members, member);
        //@ open member(member);
        String n1=nick.toString();
        StringBuffer b=member.nick;
        String n2=b.toString();
        hasMember = n1.equals(n2);
        //@ close member(member);
        //@ foreach_unremove(members, member);
        hasNext = iter.hasNext();
    }
    //@ iter_dispose(iter);
    //@ close room(this);
    return hasMember;
}
  public void broadcast_message(StringBuffer message)
    //@ requires room(this) &*& string_buffer(message);
    //@ ensures room(this) &*& string_buffer(message);
  {
    //@ open room(this);
    //@ assert foreach(?members0, _);
    List membersList = this.members;
    Iterator iter = membersList.iterator();
    boolean hasNext = iter.hasNext();
    //@ lengthPositive(members0);
    while (hasNext)
        //@ invariant iter(iter, membersList, ?members, ?i) &*& foreach(members, @member) &*& string_buffer(message) &*& hasNext == (i < length(members)) &*& 0 <= i &*& i <= length(members);
    {
        Object o=iter.next();
        Member member = (Member)o;
        //@ containsIth(members, i);
        //@ foreach_remove(members, member);
        //@ open member(member);
        OutputStreamWriter_ writer=member.writer;
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