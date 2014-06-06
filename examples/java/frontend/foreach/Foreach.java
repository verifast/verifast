import java.util.*;

public class Foreach
{
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    List<Integer> ints = new ArrayList<Integer>();
    Integer i1 = new Integer(1);
    Integer i2 = new Integer(2);
    Integer i3 = new Integer(3);
    Integer i4 = new Integer(4);
    ints.add(i1); ints.add(i2); ints.add(i3); ints.add(i4);

    //@ assert ints.List(?es);
    int result = 0;
    //@ ints.listToIterable();
    for (Integer x : ints)
      //@ requires i$.Iterator((seq_of_list)(es), _, ?n) &*& n >= 0 &*& n <= length(es);
      //@ ensures  i$.Iterator((seq_of_list)(es), _, length(es));
    {
      result += x.intValue();
    }
  }
}


