package chatbot;
import wrapper.net.*;
import wrapper.io.*;
public class Bot{
  public static void main(String[] args)
  //@ requires true;
  //@ ensures true;
  {
    Socket_ s = new Socket_(12345);
	
    InputStreamReader_ r = s.getReader();
    OutputStreamWriter_ w= s.getWriter();

    boolean stop = false;
    boolean test = true;

    StringBuffer line = new StringBuffer();
    StringBuffer nick = new StringBuffer();
    StringBuffer text = new StringBuffer();
    
    boolean result = false;

    r.readLine(line);
    r.readLine(line);
    r.readLine(line);
    w.write("BoT\r\n");
    while(! stop)
    //@ invariant reader(r) &*& writer(w) &*& stop ? emp : (string_buffer(line) &*& string_buffer(nick) &*& string_buffer(text));
    {
      line = new StringBuffer();
      nick = new StringBuffer();
      text = new StringBuffer();
      boolean msg=r.readLine(line);
      if(!msg){
        String l=line.toString();
        int i= l.indexOf(" says: ");
        if(i>(-1)){
          String n=l.substring(0,i);
          nick.append(n);
          int length=l.length();
          String t=l.substring(i+7,length);
          text.append(t);
          result=true;
        }else{
          result=false;
        }
        String n=nick.toString();
        test = n.equals("BoT");
        if(result && !test ){
          String t=text.toString();
          test = t.equals("!hello");
          if(test){
            w.write("Hello ");
            w.write(nick);
            w.write("!\r\n");
	  }else{
	    String q=text.toString();
	    test = q.equals("!quit");
	    if(test){
	      w.write("Byebye!\r\n");
	      w.write("");
	      stop = true;
	    }
	  }
        }
      }else{
      }
    }
    s.close_();
  }
}