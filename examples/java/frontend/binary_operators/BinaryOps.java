import java.util.*;

public class BinaryOps
{
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
     int a = 60; /* 60 = 0011 1100 */  
     int b = 13;  /* 13 = 0000 1101 */
     int c = 0;

     c = a & b;
     c = a | b;
     c = a ^ b;
     c = ~a;
     c = a << 2;
     c = a >> 2;
  }
}

