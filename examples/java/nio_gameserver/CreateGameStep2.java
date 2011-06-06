package gameserver;

import java.io.*;
import java.nio.*;
import java.nio.channels.*;
import java.util.concurrent.*;

/*@
predicate CreateGameStep2(CreateGameStep2 command, SocketChannel socket) = 
    command.gameServer |-> ?gameServer &*& gameServer != null &*& [_]GameServer(gameServer)
    &*& command.socket |-> socket &*& socket != null;
   
predicate_family_instance readstringclient(CreateGameStep2.class)(CreateGameStep2 client, SocketChannel socket) = 
    CreateGameStep2(client, socket);
 
@*/
public class CreateGameStep2 implements ReadStringClient {
    SocketChannel socket;
    GameServer gameServer;

    public void execute(String line)
    //@ requires readstringclient(CreateGameStep2.class)(this, ?s) &*& line != null &*& channel(s, 0);
    //@ ensures true;
    {
        //@ open readstringclient(CreateGameStep2.class)(this, s);
        //@ open CreateGameStep2(this, s);
        try {
            GameServer gameServer = this.gameServer;
            //@ open [?f]GameServer(gameServer);
            Semaphore semaGames = gameServer.semaGames;
            Games games = gameServer.games;
            
            //@ semaphore_simple_split(semaGames);
            
            semaGames.acquire();
            //@ open Games_ctor(games)();
            //@ open Games(games);

            if (games.count < Integer.MAX_VALUE) {
                Game game = new Game();
                game.name = line;
                game.socket = socket;

                //@ close [f]GameServer(gameServer);
                gameServer.writeToSocket("\r\nGame created, waiting for other player...\r\n", socket);

                game.next = games.head;
                games.head = game;
                games.count = games.count + 1;
                
                //@ close Game(game, games.count);
                //@ close Games(games);
                
                //@ close Games_ctor(games)();
                semaGames.release();
            }
        }
        catch (InterruptedException ex) {}
        catch (IOException ex) {}
    }
}
