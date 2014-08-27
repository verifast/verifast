public class Main
{
  public static void main(String[] args) 
    //@ requires true;
    //@ ensures true; 
  {
    int i = 0;
    
    Overloaded3 o3 = new Overloaded3();
    Overloaded2 o2 = o3;
    Overloaded1 o1 = o3;

    i = method1(o1);
    //@ assert i == 1;
    i = method1(o2);
    //@ assert i == 2;
    i = method1(o3);
    //@ assert i == 3;
    
    i = method2(o1, o1);
    //@ assert i == 11;
    i = method2(o1, o2);
    //@ assert i == 12;
    i = method2(o1, o3);
    //@ assert i == 13;
    
    i = method2(o2, o1);
    //@ assert i == 11;
    i = method2(o2, o2);
    //@ assert i == 12;
    i = method2(o2, o3);
    //@ assert i == 13;
    
    i = method2(o3, o1);
    //@ assert i == 11;
    i = method2(o3, o2);
    //@ assert i == 12;
    i = method2(o3, o3);
    //@ assert i == 13;
  }

  static int method1(Overloaded1 x)
    //@ requires true;
    //@ ensures  result == 1;
  {
    return 1;
  }
  
  static int method1(Overloaded2 x)
    //@ requires true;
    //@ ensures  result == 2;
  {
    return 2;
  }
  
  static int method1(Overloaded3 x)
    //@ requires true;
    //@ ensures  result == 3;
  {
    return 3;
  }
  
  static int method2(Overloaded1 x, Overloaded1 y)
    //@ requires true;
    //@ ensures  result == 11;
  {
    return 11;
  }
  
  static int method2(Overloaded1 x, Overloaded2 y)
    //@ requires true;
    //@ ensures  result == 12;
  {
    return 12;
  }
  
  static int method2(Overloaded1 x, Overloaded3 y)
    //@ requires true;
    //@ ensures  result == 13;
  {
    return 13;
  }
}
