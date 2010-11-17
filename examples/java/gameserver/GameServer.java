package gameserver;

import java.io.*;
import java.net.*;
import java.util.concurrent.*; 

/*@
inductive set<t1, t2, t3, t4> = set(t1, t2, t3, t4);

fixpoint t1 fst<t1, t2, t3, t4>(set<t1, t2, t3, t4> s) {
  switch(s) {
    case set(a, b, c, d):return a;
  }
}

fixpoint t2 snd<t1, t2, t3, t4>(set<t1, t2, t3, t4> s) {
  switch(s) {
    case set(a, b, c, d):return b;
  }
}

fixpoint t3 thd<t1, t2, t3, t4>(set<t1, t2, t3, t4> s) {
  switch(s) {
    case set(a, b, c, d):return c;
  }
}

fixpoint t4 fth<t1, t2, t3, t4>(set<t1, t2, t3, t4> s) {
  switch(s) {
    case set(a, b, c, d):return d;
  }
}

predicate_ctor Games_ctor(Games games)() = Games(games, ?count);

predicate_ctor Session_ctor(RPSSession session, set<InputStream, any, OutputStream, any> inout)() = RPSSession(session, inout);
@*/
 
public class GameServer {

    public boolean createGame(Socket socket, Semaphore semaphore, Games games) throws InterruptedException, IOException
    /*@ requires socket != null &*& Socket(socket, ?in, ?inInfo, ?out, ?outInfo) 
				&*& InputStream(in.getClass())(in, inInfo) &*& OutputStream(out.getClass())(out, outInfo) 
				&*& semaphore != null &*& semaphore(?f, semaphore, ?p, Games_ctor(games)); @*/
    /*@ ensures (result == false ? (Socket(socket, in, inInfo, out, outInfo)
				&*& InputStream(in.getClass())(in, inInfo) &*& OutputStream(out.getClass())(out, outInfo)) : true)
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
        } else {
            InputStream inStream = socket.getInputStream();
			//@ assert InputStream(inStream.getClass())(inStream, inInfo);
			InputStreamReader reader0 = new InputStreamReader(inStream);
			//@ InputStreamReader_upcast(reader0);
			BufferedReader reader = new BufferedReader(reader0);
			//@ assert BufferedReader(reader, reader0, ?readerInfo);
			OutputStream outStream = socket.getOutputStream();
			//@ assert OutputStream(outStream.getClass())(outStream, outInfo);
			OutputStreamWriter writer0 = new OutputStreamWriter(outStream);
			//@ OutputStreamWriter_upcast(writer0);
			BufferedWriter writer = new BufferedWriter(writer0);
			//@ BufferedWriter_upcast(writer);
			
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
			
            //@ BufferedReader_dispose(reader);
            //@ InputStreamReader_downcast(reader0, in, inInfo);
            //@ InputStreamReader_dispose(reader0);
            //@ BufferedWriter_downcast(writer, writer0, OutputStreamWriter_info(out, outInfo));
            //@ BufferedWriter_dispose(writer);
            //@ OutputStreamWriter_downcast(writer0, out, outInfo);
            //@ OutputStreamWriter_dispose(writer0);
			
            //@ close Game(game, games.count);
            //@ close Games(games, count+1);
            //@ close Games_ctor(games)();
            semaphore.release();
        
            return true;
        }
    }
    
    public void showGamesHelper(Socket socket, Game game, int count) throws IOException, InterruptedException
    /*@ requires socket != null &*& Socket(socket, ?in, ?inInfo, ?out, ?outInfo) &*& Game(game, count) &*& count >= 0
    		&*& InputStream(in.getClass())(in, inInfo) &*& OutputStream(out.getClass())(out, outInfo); @*/
    /*@ ensures Socket(socket, in, inInfo, out, outInfo) &*& Game(game, count)
    		&*& InputStream(in.getClass())(in, inInfo) &*& OutputStream(out.getClass())(out, outInfo); @*/
    {
        if (count == 0) {
        } else {
            OutputStream outStream = socket.getOutputStream();
            //@ assert OutputStream(outStream.getClass())(outStream, outInfo);
            OutputStreamWriter writer0 = new OutputStreamWriter(outStream);
            //@ OutputStreamWriter_upcast(writer0);
            BufferedWriter writer = new BufferedWriter(writer0);
            //@ BufferedWriter_upcast(writer);
            //@ open Game(game, count);
            writer.write(game.name + "\r\n");
            writer.flush();
            //@ BufferedWriter_downcast(writer, writer0, OutputStreamWriter_info(out, outInfo));
            //@ BufferedWriter_dispose(writer);
            //@ OutputStreamWriter_downcast(writer0, out, outInfo);
            //@ OutputStreamWriter_dispose(writer0);
            Game next = game.next;
            //@ open Game(next, count - 1);
            //@ close Game(next, count - 1);
            showGamesHelper(socket, game.next, count - 1);
            //@ close Game(game, count);
        }
    }

    public void showGames(Socket socket, Semaphore semaphore, Games games) throws IOException, InterruptedException
    /*@ requires socket != null &*& Socket(socket, ?in, ?inInfo, ?out, ?outInfo)  &*& games != null
    		&*& InputStream(in.getClass())(in, inInfo) &*& OutputStream(out.getClass())(out, outInfo) &*& semaphore != null
    		&*& semaphore(?f, semaphore, ?p, Games_ctor(games)); @*/
    /*@ ensures Socket(socket, in, inInfo, out, outInfo) &*& InputStream(in.getClass())(in, inInfo) 
    		&*& OutputStream(out.getClass())(out, outInfo)
    		&*& semaphore(f, semaphore, p, Games_ctor(games)); @*/
    {
        OutputStream outStream = socket.getOutputStream();
        //@ assert OutputStream(outStream.getClass())(outStream, outInfo);
        OutputStreamWriter writer0 = new OutputStreamWriter(outStream);
        //@ OutputStreamWriter_upcast(writer0);
        BufferedWriter writer = new BufferedWriter(writer0);
        //@ BufferedWriter_upcast(writer);

        semaphore.acquire();
        //@ open Games_ctor(games)();
        //@ open Games(games, ?count);

        writer.write("There are " + String.valueOf(games.count) + " available games:\r\n");

        writer.flush();
        //@ BufferedWriter_downcast(writer, writer0, OutputStreamWriter_info(out, outInfo));
        //@ BufferedWriter_dispose(writer);
        //@ OutputStreamWriter_downcast(writer0, out, outInfo);
        //@ OutputStreamWriter_dispose(writer0);
        ////@ open Games(games);
        showGamesHelper(socket, games.head, games.count);

        //@ close Games(games, count);
        //@ close Games_ctor(games)();
        semaphore.release();
    }

    

    public void getRPS(RPSSession session) throws IOException 
    /*@ requires session != null &*& RPSSession(session, ?inout); @*/
    //@ ensures RPSSession(session, inout);
    {
        //@ open RPSSession(session, inout);
        Socket socket = session.socket;
        //@ assert Socket(socket, ?in, ?inInfo, ?out, ?outInfo);
        InputStream inStream = socket.getInputStream();
        //@ assert InputStream(inStream.getClass())(inStream, inInfo);
        InputStreamReader reader0 = new InputStreamReader(inStream);
        //@ InputStreamReader_upcast(reader0);
        BufferedReader reader = new BufferedReader(reader0);
        //@ assert BufferedReader(reader, reader0, ?readerInfo);
        OutputStream outStream = socket.getOutputStream();
        //@ assert OutputStream(outStream.getClass())(outStream, outInfo);
        OutputStreamWriter writer0 = new OutputStreamWriter(outStream);
        //@ OutputStreamWriter_upcast(writer0);
        BufferedWriter writer1 = new BufferedWriter(writer0);
        //@ BufferedWriter_upcast(writer1);
        Writer writer = writer1;
        //@ assert Writer(writer.getClass())(writer, ?writerInfo);
        
        writer.write("Enter a rock (0), paper (1) or scissors (2).\r\n");
        writer.flush();
        String line = reader.readLine();
        int input = -1;
        if (line.matches("[0-2]{1}+")) {
            input = Integer.parseInt(line);
        } else {
            input = -1;
        }
        while (input < 0 || input > 2) 
        //@ invariant Writer(writer.getClass())(writer, writerInfo) &*& BufferedReader(reader, reader0, readerInfo);
        {
            writer.write("Try again.\r\n");
            writer.flush();
            input = Integer.parseInt(reader.readLine());
        }
        writer.write("Waiting for other player ...\r\n");
        writer.flush();
        session.result = input;
        //@ BufferedReader_dispose(reader);
        //@ InputStreamReader_downcast(reader0, in, inInfo);
        //@ InputStreamReader_dispose(reader0);
        //@ BufferedWriter_downcast(writer1, writer0, OutputStreamWriter_info(out, outInfo));
        //@ BufferedWriter_dispose(writer1);
        //@ OutputStreamWriter_downcast(writer0, out, outInfo);
        //@ OutputStreamWriter_dispose(writer0);
        //@ close RPSSession(session, inout);
    }



    public void playGame(Socket socket1, Socket socket2) throws IOException, InterruptedException 
    /*@ requires socket1 != null &*& socket2 != null &*& Socket(socket1, ?in1, ?inInfo1, ?out1, ?outInfo1) 
    		&*& Socket(socket2, ?in2, ?inInfo2, ?out2, ?outInfo2) &*& InputStream(in1.getClass())(in1, inInfo1)
    		&*& InputStream(in2.getClass())(in2, inInfo2) &*& OutputStream(out1.getClass())(out1, outInfo1) 
    		&*& OutputStream(out2.getClass())(out2, outInfo2); @*/
    /*@ ensures Socket(socket1, in1, inInfo1, out1, outInfo1) 
    		&*& Socket(socket2, in2, inInfo2, out2, outInfo2) &*& InputStream(in1.getClass())(in1, inInfo1)
    		&*& InputStream(in2.getClass())(in2, inInfo2) &*& OutputStream(out1.getClass())(out1, outInfo1) 
    		&*& OutputStream(out2.getClass())(out2, outInfo2); @*/
    {
        boolean finished = false;

        while (!finished) 
        /*@ invariant Socket(socket1, in1, inInfo1, out1, outInfo1) &*& Socket(socket2, in2, inInfo2, out2, outInfo2) 
    		&*& OutputStream(out1.getClass())(out1, outInfo1) &*& OutputStream(out2.getClass())(out2, outInfo2)
    		&*& InputStream(in1.getClass())(in1, inInfo1) &*& InputStream(in2.getClass())(in2, inInfo2); @*/
        {
            RPSSession session1 = new RPSSession();
            session1.socket = socket1;
            //@ close RPSSession(session1, set(in1, inInfo1, out1, outInfo1));
            //@ close n_times(0, Session_ctor(session1, set(in1, inInfo1, out1, outInfo1)));
            Semaphore semaphore = new Semaphore(0);
            //@  semaphore_split_detailed(semaphore, 1/2, 0);
            GetRockPaperScissorsAsync async = new GetRockPaperScissorsAsync();
            async.session = session1;
            async.gameServer = this;
            async.semaphore_ = semaphore;
            Thread t = new Thread(async);
            //@ close GetRockPaperScissorsAsync(async, set(in1, inInfo1, out1, outInfo1));
            //@ close thread_run_pre(GetRockPaperScissorsAsync.class)(async, set(in1, inInfo1, out1, outInfo1));
            t.start();
            RPSSession session2 = new RPSSession();
            session2.socket = socket2;
            //@ close RPSSession(session2, set(in2, inInfo2, out2, outInfo2));
            getRPS(session2);
            // session terug
            semaphore.acquire();
			
            //@ open Session_ctor(session1, set(in1, inInfo1, out1, outInfo1))();
            //@ open RPSSession(session1, set(in1, inInfo1, out1, outInfo1));
            //@ open RPSSession(session2, set(in2, inInfo2, out2, outInfo2));
            int choice1 = session1.result;
            int choice2 = session2.result;
            
            OutputStream outStream1 = socket1.getOutputStream();
			//@ assert OutputStream(outStream1.getClass())(outStream1, ?outInfo);
			OutputStreamWriter writer01 = new OutputStreamWriter(outStream1);
			//@ OutputStreamWriter_upcast(writer01);
			BufferedWriter writer11 = new BufferedWriter(writer01);
			//@ BufferedWriter_upcast(writer11);
			Writer writer1 = writer11;
			//@ assert Writer(writer1.getClass())(writer1, ?writerInfo1);

			OutputStream outStream2 = socket2.getOutputStream();
			//@ assert OutputStream(outStream2.getClass())(outStream2, ?outInfo0);
			OutputStreamWriter writer02 = new OutputStreamWriter(outStream2);
			//@ OutputStreamWriter_upcast(writer02);
			BufferedWriter writer12 = new BufferedWriter(writer02);
			//@ BufferedWriter_upcast(writer12);
			Writer writer2 = writer12;
			//@ assert Writer(writer2.getClass())(writer2, ?writerInfo2);
            
            int ROCK = 0;
            int PAPER = 1;
            int SCISSORS = 2;
            
            if (choice1 == choice2) {
                writer1.write("A draw! Try again.\r\n");
                writer2.write("A draw! Try again.\r\n");
                writer1.flush();
                writer2.flush();
            } else {
                finished = true;
                if (choice1 == ROCK && choice2 == SCISSORS
                        || choice1 == PAPER && choice2 == ROCK
                        || choice1 == SCISSORS && choice2 == PAPER) {
                    writer1.write("You win.\r\n");
                    writer2.write("You lose.\r\n");
                    writer1.flush();
                    writer2.flush();
                } else {
                    writer2.write("You win.\r\n");
                    writer1.write("You lose.\r\n");
                    writer1.flush();
                    writer2.flush();
                }
            }
            
            //@ BufferedWriter_downcast(writer11, writer01, OutputStreamWriter_info(out1, outInfo1));
			//@ BufferedWriter_dispose(writer11);
			//@ OutputStreamWriter_downcast(writer01, out1, outInfo1);
            //@ OutputStreamWriter_dispose(writer01);

			//@ BufferedWriter_downcast(writer12, writer02, OutputStreamWriter_info(out2, outInfo2));
			//@ BufferedWriter_dispose(writer12);
			//@ OutputStreamWriter_downcast(writer02, out2, outInfo2);
			//@ OutputStreamWriter_dispose(writer02);
        }
    }

    public void joinGameCore(Socket socket, Semaphore semaphore, Games games, Game joinedGame) throws IOException, InterruptedException
    /*@ requires socket != null &*& Socket(socket, ?in, ?inInfo, ?out, ?outInfo) &*& InputStream(in.getClass())(in, inInfo) 
    		&*& OutputStream(out.getClass())(out, outInfo) &*& joinedGame != null &*& joinedGame.name |-> ?name
    		&*& joinedGame.socket |-> ?s &*& s != null &*& Socket(s, ?inG, ?inInfoG, ?outG, ?outInfoG) 
    		&*& InputStream(inG.getClass())(inG, inInfoG) &*& semaphore(?f, semaphore, ?p, Games_ctor(games))
    		&*& OutputStream(outG.getClass())(outG, outInfoG)&*& joinedGame.next |-> ?next &*& games != null
    		&*& semaphore != null; @*/
    /*@ ensures Socket(socket, in, inInfo, out, outInfo) &*& semaphore(_, semaphore, _, Games_ctor(games))
			&*& InputStream(in.getClass())(in, inInfo) &*& OutputStream(out.getClass())(out, outInfo); @*/
    {
        OutputStream outStream = socket.getOutputStream();
        //@ assert OutputStream(outStream.getClass())(outStream, outInfo);
        OutputStreamWriter writer0 = new OutputStreamWriter(outStream);
        //@ OutputStreamWriter_upcast(writer0);
        BufferedWriter writer1 = new BufferedWriter(writer0);
        //@ BufferedWriter_upcast(writer1);
         Writer writer = writer1;
        //@ assert Writer(writer.getClass())(writer, ?writerInfo);

        writer.write("You have joined " + joinedGame.name + ".\r\n");
        writer.flush();
        
        Socket joinedGameSocket = joinedGame.socket;
        OutputStream outStreamG = joinedGameSocket.getOutputStream();
        //@ assert OutputStream(outStreamG.getClass())(outStreamG, outInfoG);
        OutputStreamWriter writer0G = new OutputStreamWriter(outStreamG);
        //@ OutputStreamWriter_upcast(writer0G);
        BufferedWriter writerG = new BufferedWriter(writer0G);
        //@ BufferedWriter_upcast(writerG);
        Writer joinedGameWriter = writerG;
        //@ assert Writer(joinedGameWriter.getClass())(joinedGameWriter, ?writerInfoG);
        
        joinedGameWriter.write("Another player joined your game.\r\n");
        writer.flush();
        
        //@ BufferedWriter_downcast(writerG, writer0G, OutputStreamWriter_info(outStreamG, outInfoG));
        //@ BufferedWriter_dispose(writerG);
        //@ OutputStreamWriter_downcast(writer0G, outStreamG, outInfoG);
        //@ OutputStreamWriter_dispose(writer0G);
        
        //@ BufferedWriter_downcast(writer1, writer0, OutputStreamWriter_info(out, outInfo));
        //@ BufferedWriter_dispose(writer1);
        //@ OutputStreamWriter_downcast(writer0, out, outInfo);
        //@ OutputStreamWriter_dispose(writer0);
        
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

    public void joinGame(Socket socket, Semaphore semaphore, Games games) throws IOException, InterruptedException
    /*@ requires socket != null &*& Socket(socket, ?in, ?inInfo, ?out, ?outInfo) &*& InputStream(in.getClass())(in, inInfo) 
    		&*& OutputStream(out.getClass())(out, outInfo) &*& semaphore != null 
    		&*& semaphore(?f, semaphore, ?p, Games_ctor(games)); @*/
    /*@ ensures Socket(socket, in, inInfo, out, outInfo) &*& InputStream(in.getClass())(in, inInfo) 
    		&*& OutputStream(out.getClass())(out, outInfo) 
    		&*& semaphore(_, semaphore, _, Games_ctor(games)); @*/
    {
        OutputStream outStream = socket.getOutputStream();
        //@ assert OutputStream(outStream.getClass())(outStream, outInfo);
        OutputStreamWriter writer0 = new OutputStreamWriter(outStream);
        //@ OutputStreamWriter_upcast(writer0);
        BufferedWriter writer1 = new BufferedWriter(writer0);
        //@ BufferedWriter_upcast(writer1);
         Writer writer = writer1;
        //@ assert Writer(writer.getClass())(writer, ?writerInfo);
        
        semaphore.acquire();
        //@ open Games_ctor(games)();
        //@ open Games(games, ?count);
        if (games.count == 0) {
            writer.write("No game is available.\r\n");
            writer.flush();
            //@ close Games(games, count);
            //@ close Games_ctor(games)();
        
            semaphore.release();
            
            //@ BufferedWriter_downcast(writer1, writer0, OutputStreamWriter_info(out, outInfo));
            //@ BufferedWriter_dispose(writer1);
            //@ OutputStreamWriter_downcast(writer0, out, outInfo);
            //@ OutputStreamWriter_dispose(writer0);
        } else {
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
            
            //@ BufferedWriter_downcast(writer1, writer0, OutputStreamWriter_info(out, outInfo));
            //@ BufferedWriter_dispose(writer1);
            //@ OutputStreamWriter_downcast(writer0, out, outInfo);
            //@ OutputStreamWriter_dispose(writer0);

            joinGameCore(socket, semaphore, games, joinedGame);
        }
    }

    public Game selectGameHelper(Game game, int choice)
    //@ requires Game(game, ?count) &*& choice < count &*& 1 <= choice;
    /*@ ensures Game(game, count - 1) &*& result.name |-> ?name &*& result.socket |-> ?socket 
			&*& socket != null &*& Socket(socket, ?in, ?inInfo, ?out, ?outInfo)
			&*& result.next |-> ?next &*& InputStream(in.getClass())(in, inInfo) 
    		&*& OutputStream(out.getClass())(out, outInfo); @*/
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

    public void joinSelectedGame(Socket socket, Semaphore semaphore, Games games) throws IOException, InterruptedException
    /*@ requires socket != null &*& Socket(socket, ?in, ?inInfo, ?out, ?outInfo) &*& InputStream(in.getClass())(in, inInfo) 
    		&*& OutputStream(out.getClass())(out, outInfo) &*& semaphore != null 
    		&*& semaphore(?f, semaphore, ?p, Games_ctor(games)); @*/
    /*@ ensures Socket(socket, in, inInfo, out, outInfo) &*& InputStream(in.getClass())(in, inInfo) 
    		&*& OutputStream(out.getClass())(out, outInfo) 
    		&*& semaphore(_, semaphore, _, Games_ctor(games)); @*/
    {
    	OutputStream outStream = socket.getOutputStream();
        //@ assert OutputStream(outStream.getClass())(outStream, outInfo);
        OutputStreamWriter writer0 = new OutputStreamWriter(outStream);
        //@ OutputStreamWriter_upcast(writer0);
        BufferedWriter writer1 = new BufferedWriter(writer0);
        //@ BufferedWriter_upcast(writer1);
         Writer writer = writer1;
        //@ assert Writer(writer.getClass())(writer, ?writerInfo);
    
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
            //@ BufferedWriter_downcast(writer1, writer0, OutputStreamWriter_info(out, outInfo));
            //@ BufferedWriter_dispose(writer1);
            //@ OutputStreamWriter_downcast(writer0, out, outInfo);
            //@ OutputStreamWriter_dispose(writer0);
            
        } else {
            writer.write("The following games are available.\r\n");
            writer.flush();
            
            //@ BufferedWriter_downcast(writer1, writer0, OutputStreamWriter_info(out, outInfo));
            //@ BufferedWriter_dispose(writer1);
            //@ OutputStreamWriter_downcast(writer0, out, outInfo);
            //@ OutputStreamWriter_dispose(writer0);
            
            showGamesHelper(socket, games.head, games.count);
            
            OutputStream outStream2 = socket.getOutputStream();
			//@ assert OutputStream(outStream2.getClass())(outStream2, ?outInfo2);
			OutputStreamWriter writer02 = new OutputStreamWriter(outStream2);
			//@ OutputStreamWriter_upcast(writer02);
			BufferedWriter writer12 = new BufferedWriter(writer02);
			//@ BufferedWriter_upcast(writer12);
			writer = writer12;
			//@ assert Writer(writer.getClass())(writer, ?writerInfo2);
            
            writer.write("Enter the number of the game you want to join (between 1 and " + String.valueOf(games.count) + ").\r\n");
            writer.flush();

            InputStream inStream = socket.getInputStream();
			//@ assert InputStream(inStream.getClass())(inStream, inInfo);
			InputStreamReader reader0 = new InputStreamReader(inStream);
			//@ InputStreamReader_upcast(reader0);
			BufferedReader reader = new BufferedReader(reader0);
			//@ assert BufferedReader(reader, reader0, ?readerInfo);
        
            String line = reader.readLine();
            int input = 1;
            if (line.matches("[0-9]")) {
                input = Integer.parseInt(line);
            } 
			else {
                input = -1;
            }
            
            while (input < 1 || input > games.count) 
            //@ invariant Writer(writer.getClass())(writer, writerInfo2) &*& games.count |-> count &*& BufferedReader(reader, reader0, readerInfo);
            {
                writer.write("Invalid choice. Try again.\r\n");
                writer.flush();
                input = Integer.parseInt(reader.readLine());
            }
            
            if(input == 1) {
                joinedGame = games.head;
                //@ open Game(joinedGame, ?count2);
                games.head = joinedGame.next;
            }
            else {
                joinedGame = selectGameHelper(games.head, input-1);
            }
            games.count = games.count - 1;
            Game head = games.head;
            //@ close Games(games, count - 1);
            //@ close Games_ctor(games)();
            
            semaphore.release();
            
            //@ BufferedWriter_downcast(writer12, writer02, OutputStreamWriter_info(out, outInfo));
            //@ BufferedWriter_dispose(writer12);
            //@ OutputStreamWriter_downcast(writer02, out, outInfo);
            //@ OutputStreamWriter_dispose(writer02);
            
            //@ BufferedReader_dispose(reader);
			//@ InputStreamReader_downcast(reader0, in, inInfo);
			//@ InputStreamReader_dispose(reader0);
            
            joinGameCore(socket, semaphore, games, joinedGame);
        }
    }

    public void mainMenu(Socket socket, Semaphore semaphore, Games games) throws IOException, InterruptedException
    /*@ requires socket != null &*& Socket(socket, ?in, ?inInfo, ?out, ?outInfo) &*& InputStream(in.getClass())(in, inInfo) 
    		&*& OutputStream(out.getClass())(out, outInfo) &*& semaphore != null 
    		&*& semaphore(?f, semaphore, ?p, Games_ctor(games)) &*& games != null; @*/
    /*@ ensures true; @*/
    {
        boolean quit = false;
        
        while (!quit) 
        /*@ invariant quit ? true : (socket != null &*& Socket(socket, in, inInfo, out, outInfo) 
        	&*& InputStream(in.getClass())(in, inInfo) 
    		&*& OutputStream(out.getClass())(out, outInfo) 
    		&*& semaphore(_, semaphore, _, Games_ctor(games)) &*& games != null  &*& semaphore != null); @*/
        {
			OutputStream outStream = socket.getOutputStream();
			//@ assert OutputStream(outStream.getClass())(outStream, outInfo);
			OutputStreamWriter writer0 = new OutputStreamWriter(outStream);
			//@ OutputStreamWriter_upcast(writer0);
			BufferedWriter writer1 = new BufferedWriter(writer0);
			//@ BufferedWriter_upcast(writer1);
			 Writer writer = writer1;
			//@ assert Writer(writer.getClass())(writer, ?writerInfo);
			
			InputStream inStream = socket.getInputStream();
			//@ assert InputStream(inStream.getClass())(inStream, inInfo);
			InputStreamReader reader0 = new InputStreamReader(inStream);
			//@ InputStreamReader_upcast(reader0);
			BufferedReader reader = new BufferedReader(reader0);
			//@ assert BufferedReader(reader, reader0, ?readerInfo);
                
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
            } else {
            input = -1;
            }
            
            
			//@ BufferedReader_dispose(reader);
            //@ InputStreamReader_downcast(reader0, in, inInfo);
            //@ InputStreamReader_dispose(reader0);

            //@ BufferedWriter_downcast(writer1, writer0, OutputStreamWriter_info(out, outInfo));
            //@ BufferedWriter_dispose(writer1);
            //@ OutputStreamWriter_downcast(writer0, out, outInfo);
            //@ OutputStreamWriter_dispose(writer0);
            
            if (input == 1) {
                
                if (createGame(socket, semaphore, games)) {
                    quit = true;
                } 
				else {
                    outStream = socket.getOutputStream();
                    //@ assert OutputStream(outStream.getClass())(outStream, outInfo);
                    writer0 = new OutputStreamWriter(outStream);
                    //@ OutputStreamWriter_upcast(writer0);
                    writer1 = new BufferedWriter(writer0);
                    //@ BufferedWriter_upcast(writer1);
                    writer = writer1;
                    //@ assert Writer(writer.getClass())(writer, ?writerInfo2);

                    inStream = socket.getInputStream();
                    //@ assert InputStream(inStream.getClass())(inStream, inInfo);
                    reader0 = new InputStreamReader(inStream);
                    //@ InputStreamReader_upcast(reader0);
                    reader = new BufferedReader(reader0);
                    //@ assert BufferedReader(reader, reader0, readerInfo);

                    writer.write("Insufficient space. Try again later.");
                    writer.flush();
                    
                    //@ BufferedReader_dispose(reader);
					//@ InputStreamReader_downcast(reader0, in, inInfo);
					//@ InputStreamReader_dispose(reader0);

					//@ BufferedWriter_downcast(writer1, writer0, OutputStreamWriter_info(out, outInfo));
					//@ BufferedWriter_dispose(writer1);
					//@ OutputStreamWriter_downcast(writer0, out, outInfo);
					//@ OutputStreamWriter_dispose(writer0);
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
				outStream = socket.getOutputStream();
                //@ assert OutputStream(outStream.getClass())(outStream, outInfo);
                writer0 = new OutputStreamWriter(outStream);
                //@ OutputStreamWriter_upcast(writer0);
                writer1 = new BufferedWriter(writer0);
                //@ BufferedWriter_upcast(writer1);
                writer = writer1;
                //@ assert Writer(writer.getClass())(writer, ?writerInfo2);

                inStream = socket.getInputStream();
                //@ assert InputStream(inStream.getClass())(inStream, inInfo);
                reader0 = new InputStreamReader(inStream);
                //@ InputStreamReader_upcast(reader0);
                reader = new BufferedReader(reader0);
                //@ assert BufferedReader(reader, reader0, readerInfo);
                writer.write("Bye!\r\n");
                writer.flush();
                //@ BufferedReader_dispose(reader);
                //@ InputStreamReader_downcast(reader0, in, inInfo);
                //@ InputStreamReader_dispose(reader0);

                //@ BufferedWriter_downcast(writer1, writer0, OutputStreamWriter_info(out, outInfo));
                //@ BufferedWriter_dispose(writer1);
                //@ OutputStreamWriter_downcast(writer0, out, outInfo);
                //@ OutputStreamWriter_dispose(writer0);
                socket.close();
                quit = true;
            } 
			else if (input == 6) {
				//@ assert OutputStream(outStream.getClass())(outStream, outInfo);
                writer0 = new OutputStreamWriter(outStream);
                //@ OutputStreamWriter_upcast(writer0);
                writer1 = new BufferedWriter(writer0);
                //@ BufferedWriter_upcast(writer1);
                writer = writer1;
                //@ assert Writer(writer.getClass())(writer, ?writerInfo2);

				inStream = socket.getInputStream();
                //@ assert InputStream(inStream.getClass())(inStream, inInfo);
                reader0 = new InputStreamReader(inStream);
                //@ InputStreamReader_upcast(reader0);
                reader = new BufferedReader(reader0);
                //@ assert BufferedReader(reader, reader0, readerInfo);
                writer.write("Function not supported yet!\r\n");
                writer.flush();
                //@ BufferedReader_dispose(reader);
                //@ InputStreamReader_downcast(reader0, in, inInfo);
                //@ InputStreamReader_dispose(reader0);

                //@ BufferedWriter_downcast(writer1, writer0, OutputStreamWriter_info(out, outInfo));
                //@ BufferedWriter_dispose(writer1);
                //@ OutputStreamWriter_downcast(writer0, out, outInfo);
                //@ OutputStreamWriter_dispose(writer0);
            } else {
				//@ assert OutputStream(outStream.getClass())(outStream, outInfo);
                writer0 = new OutputStreamWriter(outStream);
                //@ OutputStreamWriter_upcast(writer0);
                writer1 = new BufferedWriter(writer0);
                //@ BufferedWriter_upcast(writer1);
                writer = writer1;
                //@ assert Writer(writer.getClass())(writer, ?writerInfo2);

				inStream = socket.getInputStream();
                //@ assert InputStream(inStream.getClass())(inStream, inInfo);
                reader0 = new InputStreamReader(inStream);
                //@ InputStreamReader_upcast(reader0);
                reader = new BufferedReader(reader0);
                //@ assert BufferedReader(reader, reader0, readerInfo);
                writer.write("Invalid choice. Try again.\r\n");
                writer.flush();
                //@ BufferedReader_dispose(reader);
                //@ InputStreamReader_downcast(reader0, in, inInfo);
                //@ InputStreamReader_dispose(reader0);

                //@ BufferedWriter_downcast(writer1, writer0, OutputStreamWriter_info(out, outInfo));
                //@ BufferedWriter_dispose(writer1);
                //@ OutputStreamWriter_downcast(writer0, out, outInfo);
                //@ OutputStreamWriter_dispose(writer0);
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
            Socket socket = serverSocket.accept();
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
