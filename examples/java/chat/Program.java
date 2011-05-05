package chat;

import java.io.*;
import java.net.*;
import java.util.*;
import java.util.concurrent.*;

public class Program {
    public static void main(String[] args) throws IOException /*@ ensures true; @*/
        //@ requires true;
        //@ ensures true;
    {
        Room room = new Room();
        //@ close room_ctor(room)();
        //@ close n_times(0, room_ctor(room));
        //@ close n_times(1, room_ctor(room));
        Semaphore roomLock = new Semaphore(1);
        ServerSocket serverSocket = new ServerSocket(12345);

        while (true)
            //@ invariant semaphore(?f, roomLock, ?p, room_ctor(room)) &*& ServerSocket(serverSocket);
        {
            Socket socket = serverSocket.accept();
            //@ semaphore_split(roomLock); // tweede versie split moeten toevoegen want: semaphore_split_detailed(roomLock, f/2, 0) werkt niet.
            Session session = new Session(room, roomLock, socket);
            //@ close thread_run_pre(Session.class)(session, unit);
            Thread t = new Thread(session);
            t.start();
        }
    }
}