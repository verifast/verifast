package gameserver;

/*@
predicate Game(Game game, int count) = 
        game == null ? count == 0 : count > 0 &*& game.name |-> ?name 
        &*& game.socket |-> ?socket &*& socket != null &*& bufferedsocket(socket, ?reader, ?writer)
        &*& game.next |-> ?next &*& Game(next, count - 1);
@*/

public class Game {
    String name;
    BufferedSocket socket;
    Game next;
}
