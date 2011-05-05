package gameserver;

import java.io.IOException;

public class Main {
    public static void main(String[] args) throws IOException /*@ ensures true; @*/
    //@ requires true;
    //@ ensures true;
    {
        GameServer server = new GameServer();
        server.startServer();
    }
}
