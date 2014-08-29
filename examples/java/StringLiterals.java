//@ predicate charsInString(String s, list<char> cs) = cs == charsOfString(s);

public class StringLiterals
{
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    String foo = "Foo";
    String bar = "Bar";
    
    method(foo);
    method(bar);
    
    methodFoo(foo);
    int i = 0;
    //@ assert i == 0;
    i = methodBar(foo);
    //@ assert i == -1;
    i = methodBar(bar);
    //@ assert i == 1;
  }
  
  static public void method(String s)
    //@ requires true;
    //@ ensures  charsInString(s, charsOfString(s));
  {
    //@ close charsInString(s, charsOfString(s));
  }
  
  static public void methodFoo(String s)
    //@ requires charsOfString(s) == "Foo";
    //@ ensures  true;
  {
  }
  
  static int methodBar(String s)
    //@ requires s != null;
    //@ ensures  result == (charsOfString(s) == "Bar" ? 1 : -1);
  {
    if (s.equals("Bar"))
      return 1;
    else
      return -1;
  }
}
 