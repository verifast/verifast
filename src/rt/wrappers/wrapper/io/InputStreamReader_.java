package wrapper.io;

import java.io.*;
public class InputStreamReader_{
  BufferedReader reader;
  public InputStreamReader_(InputStream i){
    reader=new BufferedReader(new InputStreamReader(i));
  }
  public boolean readLine(StringBuffer buffer){
    String s;
    try{
      s=reader.readLine();
    }catch(IOException e){
      throw new RuntimeException("IOException ");
    }
    if(s==null || s.length()==0){
    return true;
    }
	buffer.setLength(0);
    buffer.append(s);
    System.out.println(s);
    return false;
  }
  public void close() throws IOException{
    reader.close();
  }
}