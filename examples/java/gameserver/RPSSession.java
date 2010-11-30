package gameserver;

import java.io.*;
import java.net.*;

/*@
predicate RPSSession(RPSSession session, BufferedReader r, BufferedWriter w) = 
        session == null ? emp : session.result |-> ?result &*& 0 <= result &*& result <= 2
        &*& [1/2]session.socket |-> ?socket &*& socket != null
        &*& bufferedsocket(socket, r, w);
@*/

public class RPSSession {
    BufferedSocket socket;
    int result;
}
