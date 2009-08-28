package chatbot;

import wrapper.net.*;
import wrapper.io.*;

public class Bot {
    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Socket_ s = new Socket_(12345);
      
        InputStreamReader_ r = s.getReader();
        OutputStreamWriter_ w = s.getWriter();

        r.readLine();
        r.readLine();
        r.readLine();
        
        w.write("BoT\r\n");
        
        boolean stop = false;
        while (!stop)
            //@ invariant reader(r) &*& writer(w);
        {
            String line = r.readLine();
            if (line != null) {
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
                        } else {
                            boolean isQuit = text.equals("!quit");
                            if (isQuit) {
                                w.write("Byebye!\r\n");
                                stop = true;
                            }
                        }
                    }
                }
            }
        }
        s.close_();
    }
}