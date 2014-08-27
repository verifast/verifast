public class Main
{
  public static void main(String[] args) 
    //@ requires true;
    //@ ensures true; 
  {
    Super o = new Sub();
    int i = 0;
    i = o.increment(i);
    //@ assert i == 1;
  }
}
