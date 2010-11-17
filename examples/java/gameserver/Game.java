package gameserver;

import java.net.*;
import java.io.*;
 
/*@
predicate Game(Game game, int count) = 
	game == null ? count == 0 : count > 0 &*& game.name |-> ?name &*& game.socket |-> ?socket 
	&*& socket != null &*& Socket(socket, ?in, ?inInfo, ?out, ?outInfo)
	&*& game.next |-> ?next &*& Game(next, count - 1) 
	&*& InputStream(in.getClass())(in, inInfo) &*& OutputStream(out.getClass())(out, outInfo);
@*/

public class Game {
    String name;
    Socket socket;
    Game next;
}
