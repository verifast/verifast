import java.io.*;
import java.util.*;

class Program {
    static void readLinesIntoList(BufferedReader reader, List list)
        //@ requires BufferedReader(reader, ?reader0, ?info) &*& reader != null &*& list(list, _) &*& list != null;
        //@ ensures BufferedReader(reader, reader0, info) &*& list(list, _);
    {
        boolean repeat = true;
        do
            //@ invariant BufferedReader(reader, reader0, info) &*& list(list, _);
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