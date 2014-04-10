public class LocalClass_desugared
{
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;  
  {
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    first.setX(111);
    int i = first.getX();
    /*@ assert i == 111;@*/
  }
}

class LocalClass_desugared$1InnerClass 
{
  //@ predicate LocalClass_desugared$1InnerClass(int x) = this.x |-> x; 
  
  int x = 1;
    
  LocalClass_desugared$1InnerClass()    
    //@ requires true;
    //@ ensures  LocalClass_desugared$1InnerClass(1);
  {
    super();
    //@ close LocalClass_desugared$1InnerClass(1);
  }
    
  int getX()    
    //@ requires LocalClass_desugared$1InnerClass(?x);
    //@ ensures LocalClass_desugared$1InnerClass(x) &*& result == x;
  {
    //@ open LocalClass_desugared$1InnerClass(x);
    return this.x;
  }
    
  void setX(int i)    
    //@ requires LocalClass_desugared$1InnerClass(_);
    //@ ensures LocalClass_desugared$1InnerClass(i);
  {
    x = i;
  }
}
