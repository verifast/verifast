package gameserver;

import java.nio.channels.*;

/*@
predicate gamestatus(GameStatus status, SocketChannel player1, SocketChannel player2) = 
    status.player1 |-> player1 &*& player1 != null
    &*& status.player2 |-> player2 &*& player2 != null
    &*& status.player1Choice |-> ?player1Choice
    &*& status.player2Choice |-> ?player2Choice
    &*& status.player1HasPlayed |-> ?player1HasPlayed
    &*& status.player2HasPlayed |-> ?player2HasPlayed
    &*& (player1HasPlayed == true ? channel(player1, 0) : true) 
    &*& (player2HasPlayed == true ? channel(player2, 0) : true);
    
predicate_ctor gamestatus_ctor(GameStatus status, SocketChannel player1, SocketChannel player2)() = gamestatus(status, player1, player2);

predicate gamestatus_ctor_args(SocketChannel player1, SocketChannel player2) = true;
@*/

public class GameStatus {
    SocketChannel player1;
    SocketChannel player2;
    int player1Choice;
    int player2Choice;
    boolean player1HasPlayed;
    boolean player2HasPlayed;
}
