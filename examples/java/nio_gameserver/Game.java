package gameserver;

import java.nio.channels.*;

/*@
predicate Game(Game game, int count) =
    game == null ? 
        count == 0 : 
            0 < count 
            &*& game.name |-> ?name &*& game.socket |-> ?socket
            &*& socket != null &*& channel(socket, 0)
            &*& game.next |-> ?next &*& Game(next, count - 1);
@*/
public class Game {
    String name;
    SocketChannel socket;
    Game next;
}
