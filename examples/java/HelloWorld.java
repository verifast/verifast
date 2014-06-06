public class HelloWorld 
{
  public static void main(String[] args) 
    //@ requires System_out(?o) &*& o != null;
    //@ ensures true; 
  {
    System.out.println("Hello, World");
  }
}
