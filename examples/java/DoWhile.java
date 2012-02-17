import java.io.*;
import java.util.*;

class Program {
    static void readLinesIntoList(BufferedReader reader, List list)
        //@ requires reader.Reader() &*& list.List(_);
        //@ ensures reader.Reader() &*& list.List(_);
    {
        boolean repeat = true;
        do
            //@ invariant reader.Reader() &*& list.List(_);
        {
            String line = reader.readLine();
            if (line == null)
                repeat = false;
            else
                list.add(line);
        }
        while (repeat);
    }
}