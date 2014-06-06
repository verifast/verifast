import java.util.*;

public class Foreach_desugared
{
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    List ints = new ArrayList();
    Integer i1 = new Integer(1);
    Integer i2 = new Integer(2);
    Integer i3 = new Integer(3);
    Integer i4 = new Integer(4);
    ints.add(i1); ints.add(i2); ints.add(i3); ints.add(i4);

    //@ assert ints.List(?es);
    int result = 0;
    {
      //@ ints.listToIterable();
      Iterator iSSS = ints.iterator();
      while (iSSS.hasNext())
        //@ requires iSSS.Iterator((seq_of_list)(es), _, ?n) &*& n >= 0 &*& n <= length(es);
        //@ ensures  iSSS.Iterator((seq_of_list)(es), _, length(es));
      {
        Integer x = (Integer) iSSS.next();
        {
          result += x.intValue();
        }
      }
      //@ ints.destroyIterator();
      //@ ints.iterableToList();
    }
  }
}


