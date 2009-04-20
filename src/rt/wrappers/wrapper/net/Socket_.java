package wrapper.net;

import wrapper.io.*;
import java.net.*;
import java.io.*;
public class Socket_{
  Socket s;
  InputStreamReader_ in;
  OutputStreamWriter_ out;
  public Socket_(int port){
    try{
	s=new Socket("localhost",port);
    this.in=new InputStreamReader_(s.getInputStream());
    this.out=new OutputStreamWriter_(s.getOutputStream());
    }
    catch(IOException e){throw new RuntimeException("IOException ");}
  }
  public Socket_(Socket s){
    this.s=s;
    try{
    this.in=new InputStreamReader_(s.getInputStream());
    this.out=new OutputStreamWriter_(s.getOutputStream());
    }
    catch(IOException e){throw new RuntimeException("IOException ");}
  }
  public InputStreamReader_ getReader(){
    return in;
  }
  public OutputStreamWriter_ getWriter(){
    return out;
  }
  public void close_(){
    try{
      in.close();
      out.close();
      s.close();
    }
    catch(IOException e){throw new RuntimeException("IOException ");}
  }
}