package chatbot;

import java.io.*;
import java.net.*;

public class Bot {
    public static void main(String[] args) throws IOException /*@ ensures true; @*/
        //@ requires true;
        //@ ensures true;
    {
        Socket s = new Socket("localhost", 12345);
      
        InputStream in = s.getInputStream();
        //@ assert InputStream(in.getClass())(in, ?inInfo);
        InputStreamReader reader0 = new InputStreamReader(in);
        //@ InputStreamReader_upcast(reader0);
        BufferedReader r = new BufferedReader(reader0);
        //@ assert BufferedReader(r, reader0, ?reader0Info);
        OutputStream out = s.getOutputStream();
        //@ assert OutputStream(out.getClass())(out, ?outInfo);
        OutputStreamWriter writer0 = new OutputStreamWriter(out);
        //@ OutputStreamWriter_upcast(writer0);
        Writer w = writer0;
        //@ assert Writer(w.getClass())(w, ?wInfo);

        r.readLine();
        r.readLine();
        r.readLine();
        
        w.write("BoT\r\n");
        w.flush();
        
        boolean stop = false;
        while (!stop)
            //@ invariant BufferedReader(r, reader0, reader0Info) &*& Writer(w.getClass())(w, wInfo);
        {
            String line = r.readLine();
            int index = line.indexOf(" says: ");
            if (index > -1) {
                String nick = line.substring(0, index);
                int length = line.length();
                String text = line.substring(index + 7, length);
                boolean isSelf = nick.equals("BoT");
                if (!isSelf) {
                    boolean isHello = text.equals("!hello");
                    if (isHello) {
                        w.write("Hello ");
                        w.write(nick);
                        w.write("!\r\n");
                        w.flush();
                    } else {
                        boolean isQuit = text.equals("!quit");
                        if (isQuit) {
                            w.write("Byebye!\r\n");
                            w.flush();
                            stop = true;
                        }
                    }
                }
            }
        }
        
        s.shutdownOutput();
        stop = false;
        while (!stop)
            //@ invariant BufferedReader(r, reader0, reader0Info);
        {
            String line = r.readLine();
            if (line == null) stop = true;
        }
        
        //@ BufferedReader_dispose(r);
        //@ InputStreamReader_downcast(reader0, in, inInfo);
        //@ InputStreamReader_dispose(reader0);
        //@ OutputStreamWriter_downcast(writer0, out, outInfo);
        //@ OutputStreamWriter_dispose(writer0);
        s.close();
    }
}