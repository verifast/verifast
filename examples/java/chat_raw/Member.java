package chat;

import java.io.*;
import java.net.*;
import java.util.*;

/*@

predicate member(Member member) =
    member.nick |-> ?nick &*& [1/2]member.writer |-> ?writer &*& writer != null &*& writer.Writer();

lemma void member_distinct(Member m1,Member m2)
    requires member(m1) &*& member(m2);
    ensures member(m1) &*& member(m2) &*& m1 != m2;
{
    open member(m1);
    open member(m2);
    close member(m2);
    close member(m1);
}

lemma void foreach_member_not_contains(list<Member> members, Member member)
    requires foreach(members, @member) &*& member(member);
    ensures foreach(members, @member) &*& member(member) &*& !mem<Object>(member, members);
{
    switch (members) {
        case nil:
        case cons(m, ms):
            open foreach(members, @member);
            member_distinct(m, member);
            foreach_member_not_contains(ms, member);
            close foreach(members, @member);
    }
}

@*/

class Member {
    String nick;
    Writer writer;
    
    public Member(String nick, Writer writer)
        //@ requires writer != null &*& writer.Writer();
        //@ ensures member(this) &*& [1/2]this.writer |-> writer;
    {
        this.nick = nick;
        this.writer = writer;
        //@ close member(this);
    }
}
