package wrapper.io;

import java.io.*;
public class InputStreamReader_{
  BufferedReader reader;
  public InputStreamReader_(InputStream i){
    reader=new BufferedReader(new InputStreamReader(i));
  }
  public String readLine(){
    String s;
    try{
      s=reader.readLine();
    }catch(IOException e){
      throw new RuntimeException("IOException ");
    }
    return s;
  }
  public void close() throws IOException{
    reader.close();
  }
}