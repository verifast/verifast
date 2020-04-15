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
        //@ one_time(room_ctor(room));
        Semaphore roomLock = new Semaphore(1);
        //@ roomLock.leakHandle();
        ServerSocket serverSocket = new ServerSocket(12345);

        while (true)
            //@ invariant [_]roomLock.Semaphore(room_ctor(room)) &*& serverSocket.ServerSocket();
        {
            Socket socket = serverSocket.accept();
            Session session = new Session(room, roomLock, socket);
            //@ close session.pre();
            Thread t = new Thread(session);
            t.start();
        }
    }
}