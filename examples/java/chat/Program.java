package chat;

import java.util.*;
import java.util.concurrent.*;
import wrapper.io.*;
import wrapper.net.*;

public class Program {
    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Room room = new Room();
        //@ close room_ctor(room)();
        //@ close create_lock_ghost_arg(room_ctor(room));
        Semaphore roomLock = new Semaphore(1);
        ServerSocket_ serverSocket = new ServerSocket_(12345);

        while (true)
            //@ invariant [_]lock(roomLock, room_ctor(room)) &*& server_socket(serverSocket);
        {
            Socket_ socket = serverSocket.accept();
            //@ split_fraction lock(roomLock, _);
            Session session = new Session(room, roomLock, socket);
            //@ close thread_run_pre(Session.class)(session,unit);
            Thread t = new Thread(session);
            t.start();
        }
    }
}