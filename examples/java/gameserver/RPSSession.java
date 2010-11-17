package gameserver;

import java.net.*;
import java.io.*;

/*@
predicate RPSSession(RPSSession session, set<InputStream, any, OutputStream, any> inout) = 
	session == null ? emp : session.result |-> ?result &*& 0 <= result &*& result <= 2 
	&*& [1/2]session.socket |-> ?socket &*& socket != null 
	&*& Socket(socket, ?in, ?inInfo, ?out, ?outInfo) &*& InputStream(in.getClass())(in, inInfo) 
	&*& OutputStream(out.getClass())(out, outInfo) &*& in == fst(inout) &*& inInfo == snd(inout) 
	&*& out == thd(inout) &*& outInfo == fth(inout);
@*/

public class RPSSession {
    Socket socket;
    int result;
}
