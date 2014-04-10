interface AnonymousInterface
{
  int increment(int i);    
    //@ requires true;
    //@ ensures result == i + 1;
    
  int decrement(int i);    
    //@ requires true;
    //@ ensures result == i - 1;
}

public class AnonymousClass_desugared
{    
  public static void main(String[] args)    
    //@ requires true;
    //@ ensures true;
  {
    AnonymousInterface inner = new AnonymousClass_desugared$1();
    
    int i = 0;
    i = inner.increment(100);
    //@ assert i == 101;
    i = inner.increment(i);
    //@ assert i == 102;
    i = inner.decrement(i);
    //@ assert i == 101;
    i = inner.decrement(i);
    //@ assert i == 100;
  }
}

class AnonymousClass_desugared$1 implements AnonymousInterface 
{
  public int increment(int i)    
    //@ requires true;
    //@ ensures result == i + 1;
  {
    return i + 1;
  }
    
  public int decrement(int i)    
    //@ requires true;
    //@ ensures result == i - 1;
  {
    return i - 1;
  }
}
