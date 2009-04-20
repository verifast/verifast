package chat;

import java.util.*;
import wrapper.net.*;
import wrapper.io.*;
/*@
predicate member(Member member)
    requires member.nick |-> ?nick &*& member.writer |-> ?writer &*& string_buffer(nick) &*& writer(writer);

lemma void member_distinct(Member m1,Member m2)
    requires member(m1) &*& member(m2);
    ensures member(m1) &*& member(m2) &*& m1 != m2;
{
    open member(m1);
    open member(m2);
    close member(m2);
    close member(m1);
}

lemma void foreach_member_not_contains(listval members,Member member)
    requires foreach(members, @member) &*& member(member);
    ensures foreach(members, @member) &*& member(member) &*& !contains(members, member);
{
    switch (members) {
        case nil:
        case cons(member0, members0):
            open foreach(members, @member);
            member_distinct((Member)member0, member);
            foreach_member_not_contains(members0, member);
            close foreach(members, @member);
    }
}
@*/
class Member{
  StringBuffer nick;
  OutputStreamWriter_ writer;
  public Member(StringBuffer nick,OutputStreamWriter_ writer)
  //@ requires [?f]string_buffer(nick)&*& writer(writer);
  //@ ensures member(result);
  {
    StringBuffer nickCopy=new StringBuffer();
    nickCopy.append(nick);
    this.nick = nickCopy;
    this.writer = writer;
    //@ close member(this);
  }
}
