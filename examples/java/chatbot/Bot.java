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
        InputStreamReader reader0 = new InputStreamReader(in);
        BufferedReader r = new BufferedReader(reader0);
        OutputStream out = s.getOutputStream();
        OutputStreamWriter writer0 = new OutputStreamWriter(out);
        Writer w = writer0;

        r.readLine();
        r.readLine();
        r.readLine();
        
        w.write("BoT\r\n");
        w.flush();
        
        while (true)
            //@ invariant r.Reader() &*& w.Writer();
        {
            String line = r.readLine();
            if (line == null)
                break;
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
                            break;
                        }
                    }
                }
            }
        }
        
        s.shutdownOutput();
        while (true)
            //@ invariant r.Reader();
        {
            String line = r.readLine();
            if (line == null)
                break;
        }
        
        //@ r.destroy();
        //@ reader0.destroy();
        //@ writer0.destroy();
        s.close();
    }
}