package wrapper.net;
import wrapper.io.*;
import java.net.*;
import java.io.*;
public class ServerSocket_{
  ServerSocket s;
  public ServerSocket_(int port){
    try{s=new ServerSocket(port);}
    catch(IOException e){throw new RuntimeException("IOException ");}
  }
  public Socket_ accept(){
    Socket_ result;
    try{result=new Socket_(s.accept());}
    catch(IOException e){throw new RuntimeException("IOException ");}
    return result;
  }
}