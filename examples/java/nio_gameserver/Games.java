package gameserver;

/*@
predicate Games(Games games) = 
    games.head |-> ?head &*& games.count |-> ?count &*& count >= 0 &*& Game(head, count);

predicate_ctor Games_ctor(Games games)() = Games(games);
@*/ 
public class Games {
    Game head;
    int count;
}
