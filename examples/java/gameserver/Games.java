package gameserver;

/*@
predicate Games(Games games, int count) = 
        games.head |-> ?head &*& games.count |-> count &*& count >= 0 &*& Game(head, count);
@*/

public class Games {
    Game head;
    int count;
}
