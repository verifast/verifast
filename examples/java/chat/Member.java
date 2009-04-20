package chat;

import java.util.*;
import wrapper.net.*;
import wrapper.io.*;

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
