package gameserver;

import java.nio.channels.*;

/*@
predicate_family readstringclient(Class c)(ReadStringClient run, SocketChannel socket);
@*/

public interface ReadStringClient {
    public void execute(String line);
    //@ requires readstringclient(this.getClass())(this, ?socket) &*& line != null &*& channel(socket, 0);
    //@ ensures true;
}