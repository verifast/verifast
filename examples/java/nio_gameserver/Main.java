package gameserver;

public class Main {

    public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    {
        GameServer server = new GameServer();
        //@ close GameServerTemp(server);
        server.startServer();
    }
}
