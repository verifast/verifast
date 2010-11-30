package gameserver;

import java.io.*;
import java.net.*;

/*@
predicate bufferedsocket(BufferedSocket s, BufferedReader reader, BufferedWriter writer) = 
        s != null &*& s.socket |-> ?socket &*& s.reader |-> reader &*& s.writer |-> writer
        &*& s.inStream |-> ?inStream &*& s.reader0 |-> ?reader0 
        &*& s.outStream |-> ?outStream &*& s.writer0 |-> ?writer0
        &*& socket != null &*& reader != null &*& writer != null
        &*& Socket(socket, ?in, ?inInfo, ?out, ?outInfo)
        &*& Writer(writer.getClass())(writer, BufferedWriter_info(writer0, OutputStreamWriter_info(out, outInfo))) 
        &*& BufferedReader(reader, reader0, InputStreamReader_info(in, inInfo));
@*/

public class BufferedSocket {
    Socket socket;
    BufferedReader reader;
    BufferedWriter writer;
    InputStream inStream;
    InputStreamReader reader0;
    OutputStream outStream;
    OutputStreamWriter writer0;
    
    public BufferedSocket(Socket socket) throws IOException 
    /*@ requires socket != null &*& Socket(socket, ?in, ?inInfo, ?out, ?outInfo) 
            &*& InputStream(in.getClass())(in, inInfo) 
            &*& OutputStream(out.getClass())(out, outInfo); @*/
    //@ ensures bufferedsocket(this, ?reader, ?writer);
    {
        this.socket = socket;

        InputStream inStream = socket.getInputStream();
        //@ assert InputStream(inStream.getClass())(inStream, inInfo);
        InputStreamReader reader0 = new InputStreamReader(inStream);
        //@ InputStreamReader_upcast(reader0);
        BufferedReader reader = new BufferedReader(reader0);
        //@ assert BufferedReader(reader, reader0, ?readerInfo);
        
        OutputStream outStream = socket.getOutputStream();
        //@ assert OutputStream(outStream.getClass())(outStream, outInfo);
        OutputStreamWriter writer0 = new OutputStreamWriter(outStream);
        //@ OutputStreamWriter_upcast(writer0);
        BufferedWriter writer = new BufferedWriter(writer0);
        //@ BufferedWriter_upcast(writer);

        this.inStream = inStream;
        this.reader0 = reader0;
        this.reader = reader;
        this.outStream = outStream;
        this.writer0 = writer0;
        this.writer = writer;
        
        //@ close bufferedsocket(this, reader, writer);
    }

    public BufferedReader getReader() 
    //@ requires bufferedsocket(this, ?reader, ?writer);
    //@ ensures bufferedsocket(this, reader, writer) &*& result != null &*& result == reader;
    {
        //@ open bufferedsocket(this, reader, writer);
        BufferedReader r = this.reader;
        //@ close bufferedsocket(this, reader, writer);
        return r;
    }

    public BufferedWriter getWriter() 
    //@ requires bufferedsocket(this, ?reader, ?writer);
    //@ ensures bufferedsocket(this, reader, writer) &*& result != null &*& result == writer;
    {
        //@ open bufferedsocket(this, reader, writer);
        BufferedWriter w = this.writer;
        //@ close bufferedsocket(this, reader, writer);
        return w;
    }

    public void close() throws IOException 
    //@ requires bufferedsocket(this, ?r, ?w);
    //@ ensures true;
    {
        //@ open bufferedsocket(this, r, w);
    
        Socket socket = this.socket;
        BufferedReader reader = this.reader;
        BufferedWriter writer = this.writer;
        InputStream inStream = this.inStream;
        InputStreamReader reader0 = this.reader0;
        OutputStream outStream = this.outStream;
        OutputStreamWriter writer0 = this.writer0;           
 
        //@ assert Socket(socket, ?in, ?inInfo, ?out, ?outInfo);
        
        //@ BufferedReader_dispose(reader);        
        //@ InputStreamReader_downcast(reader0, in, inInfo);
        //@ InputStreamReader_dispose(reader0);
        
        //@ BufferedWriter_downcast(writer, writer0, OutputStreamWriter_info(out, outInfo));
        //@ BufferedWriter_dispose(writer);
        //@ OutputStreamWriter_downcast(writer0, out, outInfo);
        //@ OutputStreamWriter_dispose(writer0);
        
        socket.close();
    }
}
