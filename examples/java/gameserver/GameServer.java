package gameserver;

import java.io.*;
import java.net.*;
import java.util.concurrent.*;

/*@
inductive set<t1, t2> = set(t1, t2);

fixpoint t1 fst<t1, t2>(set<t1, t2> s) {
    switch(s) {
        case set(a, b):return a;
    }
}

fixpoint t2 snd<t1, t2>(set<t1, t2> s) {
    switch(s) {
        case set(a, b):return b;
    }
}

predicate_ctor Games_ctor(Games games)() = Games(games, ?count);

predicate_ctor Session_ctor(RPSSession session, BufferedReader r, BufferedWriter w)() = RPSSession(session, r, w);
@*/

public class GameServer {
    public boolean createGame(BufferedSocket socket, Semaphore semaphore, Games games) throws InterruptedException, IOException
    /*@ requires socket != null &*& bufferedsocket(socket, ?r, ?w) &*& semaphore != null 
    &*& semaphore(?f, semaphore, ?p, Games_ctor(games)); @*/
    /*@ ensures (result == false ? bufferedsocket(socket, r, w) : true)
    &*& semaphore(f, semaphore, p, Games_ctor(games)); @*/
    {
        semaphore.acquire();
        //@ open Games_ctor(games)();
        //@ open Games(games, ?count);
        if (games.count == Integer.MAX_VALUE) {
            //@ close Games(games, count);
            //@ close Games_ctor(games)();
            semaphore.release();
            return false;
        }
        else {
            BufferedReader reader = socket.getReader();
            BufferedWriter writer = socket.getWriter();
            
            //@ open bufferedsocket(socket, r, w);

            writer.write("Enter the name of your game.\r\n");
            writer.flush();
            String name = reader.readLine();
            Game game = new Game();
            game.name = name;
            game.socket = socket;
            writer.write("Game created, waiting for other player...\r\n");
            writer.flush();
            game.next = games.head;
            games.head = game;
            games.count = games.count + 1;
            
            //@ close bufferedsocket(socket, r, w);
            //@ close Game(game, games.count);
            //@ close Games(games, count+1);
            //@ close Games_ctor(games)();
            semaphore.release();

            return true;
        }
    }

    public void showGamesHelper(BufferedSocket socket, Game game, int count) throws IOException, InterruptedException
    /*@ requires socket != null &*& bufferedsocket(socket, ?r, ?w) &*& Game(game, count) &*& count >= 0; @*/
    /*@ ensures bufferedsocket(socket, r, w) &*& Game(game, count); @*/
    {
        if (count == 0) {
        }
        else {
            BufferedWriter writer = socket.getWriter();
            //@ open bufferedsocket(socket, r, w);
            //@ open Game(game, count);
            writer.write(game.name + "\r\n");
            writer.flush();
            //@ close bufferedsocket(socket, r, w);

            Game next = game.next;
            //@ open Game(next, count - 1);
            //@ close Game(next, count - 1);
            showGamesHelper(socket, game.next, count - 1);
            //@ close Game(game, count);
        }
    }

    public void showGames(BufferedSocket socket, Semaphore semaphore, Games games) throws IOException, InterruptedException
    /*@ requires socket != null &*& bufferedsocket(socket, ?r, ?w)  &*& games != null &*& semaphore != null
    &*& semaphore(?f, semaphore, ?p, Games_ctor(games)); @*/
    /*@ ensures bufferedsocket(socket, r, w) &*& semaphore(f, semaphore, p, Games_ctor(games)); @*/
    {
        BufferedWriter writer = socket.getWriter();
    //@ open bufferedsocket(socket, r, w);
        semaphore.acquire();
        //@ open Games_ctor(games)();
        //@ open Games(games, ?count);

        writer.write("There are " + String.valueOf(games.count) + " available games:\r\n");

        writer.flush();
        //@ close bufferedsocket(socket, r, w);
        showGamesHelper(socket, games.head, games.count);

        //@ close Games(games, count);
        //@ close Games_ctor(games)();
        semaphore.release();
    }

    public void getRPS(RPSSession session) throws IOException 
    //@ requires session != null &*& RPSSession(session, ?r, ?w);
    //@ ensures RPSSession(session, r, w);
    {
        //@ open RPSSession(session, r, w);
        BufferedSocket socket = session.socket;
        BufferedReader reader = socket.getReader();
        BufferedWriter writer = socket.getWriter();
        
        //@ open bufferedsocket(socket, r, w);

        writer.write("Enter a rock (0), paper (1) or scissors (2).\r\n");
        writer.flush();
        String line = reader.readLine();
        int input = -1;
        if (line.matches("[0-2]{1}+")) {
            input = Integer.parseInt(line);
        }
        else {
            input = -1;
        }

        //@ close bufferedsocket(socket, r, w);
        while (input < 0 || input > 2)
        //@ invariant bufferedsocket(socket, r, w);
        {
            //@ open bufferedsocket(socket, r, w);
            writer.write("Try again.\r\n");
            writer.flush();
            input = Integer.parseInt(reader.readLine());
            //@ close bufferedsocket(socket, r, w);
        }
        //@ open bufferedsocket(socket, r, w);
        writer.write("Waiting for other player ...\r\n");
        writer.flush();
        session.result = input;
        
        //@ close bufferedsocket(socket, r, w);
        //@ close RPSSession(session, r, w);
    }

    public void playGame(BufferedSocket socket1, BufferedSocket socket2) throws IOException, InterruptedException
    /*@ requires socket1 != null &*& socket2 != null &*& bufferedsocket(socket1, ?r1, ?w1)
    &*& bufferedsocket(socket2, ?r2, ?w2); @*/
    /*@ ensures bufferedsocket(socket1, r1, w1)
    &*& bufferedsocket(socket2, r2, w2); @*/
    {
        boolean finished = false;

        while (!finished)
        /*@ invariant bufferedsocket(socket1, r1, w1) &*& bufferedsocket(socket2, r2, w2); @*/
        {
            RPSSession session1 = new RPSSession();
            session1.socket = socket1;
            //@ close RPSSession(session1, r1, w1);
            //@ close n_times(0, Session_ctor(session1, r1, w1));
            Semaphore semaphore = new Semaphore(0);
            //@  semaphore_split_detailed(semaphore, 1/2, 0);
            GetRockPaperScissorsAsync async = new GetRockPaperScissorsAsync();
            async.session = session1;
            async.gameServer = this;
            async.semaphore_ = semaphore;
            Thread t = new Thread(async);
            //@ close GetRockPaperScissorsAsync(async, r1, w1);
            //@ close thread_run_pre(GetRockPaperScissorsAsync.class)(async, set(r1, w1));
            t.start();
            RPSSession session2 = new RPSSession();
            session2.socket = socket2;
            //@ close RPSSession(session2, r2, w2);
            getRPS(session2);
            // session terug
            semaphore.acquire();

            //@ open Session_ctor(session1, r1, w1)();
            //@ open RPSSession(session1, r1, w1);
            //@ open RPSSession(session2, r2, w2);
            int choice1 = session1.result;
            int choice2 = session2.result;

            BufferedWriter writer1 = socket1.getWriter();
            BufferedWriter writer2 = socket2.getWriter();
            
            //@ open bufferedsocket(socket1, r1, w1);
            //@ open bufferedsocket(socket2, r2, w2);

            int ROCK = 0;
            int PAPER = 1;
            int SCISSORS = 2;

            if (choice1 == choice2) {
                writer1.write("A draw! Try again.\r\n");
                writer2.write("A draw! Try again.\r\n");
                writer1.flush();
                writer2.flush();
            }
            else {
                finished = true;
                if (choice1 == ROCK && choice2 == SCISSORS
                        || choice1 == PAPER && choice2 == ROCK
                        || choice1 == SCISSORS && choice2 == PAPER) {
                    writer1.write("You win.\r\n");
                    writer2.write("You lose.\r\n");
                    writer1.flush();
                    writer2.flush();
                }
                else {
                    writer2.write("You win.\r\n");
                    writer1.write("You lose.\r\n");
                    writer1.flush();
                    writer2.flush();
                }
            }
            
            //@ close bufferedsocket(socket1, r1, w1);
            //@ close bufferedsocket(socket2, r2, w2);
        }
    }

    public void joinGameCore(BufferedSocket socket, Semaphore semaphore, Games games, Game joinedGame) throws IOException, InterruptedException
    /*@ requires socket != null &*& bufferedsocket(socket, ?r1, ?w1) &*& joinedGame != null &*& joinedGame.name |-> ?name
    &*& joinedGame.socket |-> ?s &*& s != null &*& bufferedsocket(s, ?r2, ?w2) &*& semaphore(?f, semaphore, ?p, Games_ctor(games))
    &*& joinedGame.next |-> ?next &*& games != null &*& semaphore != null; @*/
    /*@ ensures bufferedsocket(socket, r1, w1) &*& semaphore(_, semaphore, _, Games_ctor(games)); @*/
    {
        BufferedWriter writer = socket.getWriter();
        
        //@ open bufferedsocket(socket, r1, w1);

        writer.write("You have joined " + joinedGame.name + ".\r\n");
        writer.flush();

        BufferedSocket joinedGameSocket = joinedGame.socket;
        BufferedWriter joinedGameWriter = joinedGameSocket.getWriter();
        
        //@ open bufferedsocket(s, r2, w2);

        joinedGameWriter.write("Another player joined your game.\r\n");
        writer.flush();
        
        //@ close bufferedsocket(s, r2, w2);
        //@ close bufferedsocket(socket, r1, w1);

        playGame(joinedGame.socket, socket);
        StartSession session = new StartSession();
        session.games = games;
        session.socket = joinedGame.socket;
        session.gameServer = this;
        session.semaphore = semaphore;
        Thread t = new Thread(session);

        //@ semaphore_split(semaphore);
        //@ close StartSession(session);
        //@ close thread_run_pre(StartSession.class)(session, unit);

        t.start();
    }

    public void joinGame(BufferedSocket socket, Semaphore semaphore, Games games) throws IOException, InterruptedException
    /*@ requires socket != null &*& bufferedsocket(socket, ?r, ?w) &*& semaphore != null
    &*& semaphore(?f, semaphore, ?p, Games_ctor(games)); @*/
    /*@ ensures bufferedsocket(socket, r, w) &*& semaphore(_, semaphore, _, Games_ctor(games)); @*/
    {
        BufferedWriter writer = socket.getWriter();
        //@ open bufferedsocket(socket, r, w);
        semaphore.acquire();
        //@ open Games_ctor(games)();
        //@ open Games(games, ?count);
        if (games.count == 0) {
            writer.write("No game is available.\r\n");
            writer.flush();
            //@ close Games(games, count);
            //@ close Games_ctor(games)();

            semaphore.release();
            //@ close bufferedsocket(socket, r, w);
        }
        else {
            Game joinedGame = games.head;
            //@ open Game(joinedGame, ?c);
            games.head = joinedGame.next;
            games.count = games.count - 1;
            Game head = games.head;
            int gamesCount = games.count;
            //@ open Game(head, gamesCount);
            //@ close Game(head, gamesCount);
            //@ close Games(games, count-1);
            //@ close Games_ctor(games)();
            semaphore.release();
            //@ close bufferedsocket(socket, r, w);

            joinGameCore(socket, semaphore, games, joinedGame);
        }
    }

    public Game selectGameHelper(Game game, int choice)
    //@ requires Game(game, ?count) &*& choice < count &*& 1 <= choice;
    /*@ ensures Game(game, count - 1) &*& result.name |-> ?name &*& result.socket |-> ?socket 
    &*& socket != null &*& bufferedsocket(socket, ?reader, ?writer)
    &*& result.next |-> ?next; @*/
    {
        Game joinedGame;
        //@ open Game(game, count);
        if (choice == 1) {
            joinedGame = game.next;
            //@ open Game(joinedGame, ?c);
            game.next = joinedGame.next;
        }
        else {
            joinedGame = selectGameHelper(game.next, choice - 1);
        }
        //@ close Game(game, count - 1);

        return joinedGame;
    }

    public void joinSelectedGame(BufferedSocket socket, Semaphore semaphore, Games games) throws IOException, InterruptedException
    /*@ requires socket != null &*& bufferedsocket(socket, ?r, ?w) &*& semaphore != null
    &*& semaphore(?f, semaphore, ?p, Games_ctor(games)); @*/
    /*@ ensures bufferedsocket(socket, r, w) &*& semaphore(_, semaphore, _, Games_ctor(games)); @*/
    {
        BufferedWriter writer = socket.getWriter();
        //@ open bufferedsocket(socket, r, w);

        Game joinedGame;
        semaphore.acquire();
        //@ open Games_ctor(games)();
        //@ open Games(games, ?count);
        if (games.count == 0) {
            writer.write("No game is available.\r\n");
            writer.flush();
            //@ close Games(games, count);
            //@ close Games_ctor(games)();
            semaphore.release();
            //@ close bufferedsocket(socket, r, w);
        }
        else {
            writer.write("The following games are available.\r\n");
            writer.flush();

            //@ close bufferedsocket(socket, r, w);
            showGamesHelper(socket, games.head, games.count);
            
            //@ open bufferedsocket(socket, r, w);

            writer.write("Enter the number of the game you want to join (between 1 and " + String.valueOf(games.count) + ").\r\n");
            writer.flush();
            
            //@ close bufferedsocket(socket, r, w);

            BufferedReader reader = socket.getReader();
            
            //@ open bufferedsocket(socket, r, w);

            String line = reader.readLine();
            int input = 1;
            if (line.matches("[0-9]")) {
                input = Integer.parseInt(line);
            }
            else {
                input = -1;
            }
            
            //@ close bufferedsocket(socket, r, w);

            while (input < 1 || input > games.count)
            //@ invariant bufferedsocket(socket, r, w) &*& games.count |-> count;
            {
                //@ open bufferedsocket(socket, r, w);
                writer.write("Invalid choice. Try again.\r\n");
                writer.flush();
                input = Integer.parseInt(reader.readLine());
                //@ close bufferedsocket(socket, r, w);
            }
            
            //@ open bufferedsocket(socket, r, w);

            if (input == 1) {
                joinedGame = games.head;
                //@ open Game(joinedGame, ?count2);
                games.head = joinedGame.next;
            }
            else {
                joinedGame = selectGameHelper(games.head, input - 1);
            }
            games.count = games.count - 1;
            Game head = games.head;
            //@ close Games(games, count - 1);
            //@ close Games_ctor(games)();

            semaphore.release();
            
            //@ close bufferedsocket(socket, r, w);

            joinGameCore(socket, semaphore, games, joinedGame);
        }
    }

    public void mainMenu(BufferedSocket socket, Semaphore semaphore, Games games) throws IOException, InterruptedException
    /*@ requires socket != null &*& bufferedsocket(socket, ?r, ?w) &*& semaphore != null
    &*& semaphore(?f, semaphore, ?p, Games_ctor(games)) &*& games != null; @*/ 
    /*@ ensures true; @*/
    {
        boolean quit = false;

        while (!quit)
        /*@ invariant quit ? true : (socket != null &*& bufferedsocket(socket, r, w)
        &*& semaphore(_, semaphore, _, Games_ctor(games)) &*& games != null &*& semaphore != null); @*/
        {
            BufferedReader reader = socket.getReader();
            BufferedWriter writer = socket.getWriter();
            
            //@ open bufferedsocket(socket, r, w);

            writer.write("What would you like to do?\r\n");
            writer.write("1. Create a new game.\r\n");
            writer.write("2. Show all available games.\r\n");
            writer.write("3. Join an existing game.\r\n");
            writer.write("4. Select and join an existing game.\r\n");
            writer.write("5. Quit.\r\n");
            writer.write("6. Create a new game (optional).\r\n");
            writer.flush();

            String line = reader.readLine();
            int input = -1;
            if (line.matches("[1-6]{1}+")) {
                input = Integer.parseInt(line);
            }
            else {
                input = -1;
            }
            
            //@ close bufferedsocket(socket, r, w);

            if (input == 1) {
                if (createGame(socket, semaphore, games)) {
                    quit = true;
                }
                else {

                    //@ open bufferedsocket(socket, r, w);
                    writer.write("Insufficient space. Try again later.");
                    writer.flush();
                    //@ close bufferedsocket(socket, r, w);
                }
            }
            else if (input == 2) {
                showGames(socket, semaphore, games);
            }
            else if (input == 3) {
                joinGame(socket, semaphore, games);
            }
            else if (input == 4) {
                joinSelectedGame(socket, semaphore, games);
            }
            else if (input == 5) {
                //@ open bufferedsocket(socket, r, w);
                writer.write("Bye!\r\n");
                writer.flush();
                //@ close bufferedsocket(socket, r, w);
                socket.close();
                quit = true;
            }
            else if (input == 6) {
                //@ open bufferedsocket(socket, r, w);
                writer.write("Function not supported yet!\r\n");
                writer.flush();
                //@ close bufferedsocket(socket, r, w);
            }
            else {
                //@ open bufferedsocket(socket, r, w);
                writer.write("Invalid choice. Try again.\r\n");
                writer.flush();
                //@ close bufferedsocket(socket, r, w);
            }
        }
    }

    public void startServer() throws IOException
    //@ requires true;
    //@ ensures true;
    {
        ServerSocket serverSocket = new ServerSocket(1234);
        Games games = new Games();
        games.count = 0;
        games.head = null;

        //@ close Game(null, 0);
        //@ close Games(games, 0);
        //@ close Games_ctor(games)();
        //@ close n_times(0, Games_ctor(games)); 
        //@ close n_times(1, Games_ctor(games));
        Semaphore semaphore = new Semaphore(1);
        while (true)
        //@ invariant ServerSocket(serverSocket) &*& semaphore(_, semaphore, _, Games_ctor(games));
        {
            BufferedSocket socket = new BufferedSocket(serverSocket.accept());
            StartSession session = new StartSession();
            session.gameServer = this;
            session.games = games;
            session.semaphore = semaphore;
            session.socket = socket;
            Thread t = new Thread(session);
            //@ semaphore_split(semaphore);
            //@ close StartSession(session);
            //@ close thread_run_pre(StartSession.class)(session, unit);
            t.start();
        }
    }
}
