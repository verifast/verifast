package wrapper.io;

import java.io.*;
public class OutputStreamWriter_{
  BufferedWriter writer;
  String print;
  public OutputStreamWriter_(OutputStream out){
    writer=new BufferedWriter(new OutputStreamWriter(out));
	print="";
  }
  public void write(StringBuffer buffer){
	write(buffer.toString());
  }
  public void write(String s){
    try{writer.write(s);print+=s;
	if(s.endsWith("\r\n")){
	  System.out.println(print);
	  writer.flush();
	  print="";
	}
	}
    catch(IOException e){throw new RuntimeException("IOException ");}
  }
  public void close() throws IOException{
    writer.close();
  }
}