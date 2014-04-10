import java.util.*;

public class Boxing
{
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    //Integers
    Integer i1 = 5;
    int i2 = i1;
    Integer i3 = i2;
    
    //Booleans
    Boolean bool1 = true;
    boolean bool2 = bool1;
    Boolean bool3 = bool2;
  }
}
