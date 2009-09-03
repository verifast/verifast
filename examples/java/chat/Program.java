package chat;

import java.io.*;
import java.net.*;
import java.util.*;
import java.util.concurrent.*;

public class Program {
    public static void main(String[] args) throws IOException
        //@ requires true;
        //@ ensures true;
    {
        Room room = new Room();
        //@ close room_ctor(room)();
        //@ close create_lock_ghost_arg(room_ctor(room));
        Semaphore roomLock = new Semaphore(1);
        ServerSocket serverSocket = new ServerSocket(12345);

        while (true)
            //@ invariant [_]lock(roomLock, room_ctor(room)) &*& ServerSocket(serverSocket);
        {
            Socket socket = serverSocket.accept();
            //@ split_fraction lock(roomLock, _);
            Session session = new Session(room, roomLock, socket);
            //@ close thread_run_pre(Session.class)(session, unit);
            Thread t = new Thread(session);
            t.start();
        }
    }
}