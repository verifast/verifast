import java.util.*;

public class Boxing_desugared
{
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    //Integers
    Integer i1 = Integer.valueOf(5);
    int i2 = i1.intValue();
    Integer i3 = Integer.valueOf(i2);
    
    //Booleans
    Boolean bool1 = Boolean.valueOf(true);
    boolean bool2 = bool1.booleanValue();
    Boolean bool3 = Boolean.valueOf(bool2);
  }
}
