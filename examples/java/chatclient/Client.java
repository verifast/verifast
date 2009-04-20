package chatclient;
import wrapper.net.*;
import wrapper.io.*;
import java.io.*;
public class Client{
  public static void main(String[] args)
  {
    Socket_ s = new Socket_(12345);
    InputStreamReader_ r = s.getReader();
    OutputStreamWriter_ w= s.getWriter();
    BufferedReader cmd_in = new BufferedReader(new InputStreamReader(System.in));
    boolean stop = false;

    StringBuffer line = new StringBuffer();

    String nick;
    String text;
    
    boolean result = false;

    r.readLine(line);
    r.readLine(line);
    r.readLine(line);
    try{
      nick=cmd_in.readLine();
    }catch(IOException e){
      nick="dummy";
    }
    w.write(nick+"\r\n");

    r.readLine(line);
    while(! stop)
    {
      try{
        text=cmd_in.readLine();
      }catch(IOException e){
        text="exception?";
      }

      w.write(text+"\r\n");

      if(text.equals("bye")){
        w.write("");
        stop=true;
      }else{
        r.readLine(line);
        r.readLine(line);
      }
    }
    s.close_();
  }
}