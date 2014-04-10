class OuterClass 
{
}

public class StaticMemberClass_desugared
{   
  public static void main(String[] args)    
    //@ requires class_init_token(OuterClass$InnerClass.class);
    //@ ensures true; 
  {
    //@ init_class(OuterClass$InnerClass.class);
    
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass();
    first.setX(111);
    int i = first.getX();
    /*@ assert i == 111;@*/

    first.setY(222);
    int j = second.getY();
    /*@ assert j == 222;@*/
  }
}
class OuterClass$InnerClass 
{  
  //@ predicate OuterClass$InnerClass(int x) = this.x |-> x;
  
  int x = 1;
  static int y = 1;

  OuterClass$InnerClass()
    //@ requires true;
    //@ ensures  OuterClass$InnerClass(1);
  {
    //@ close OuterClass$InnerClass(1);
  }
    
  int getX()    
    //@ requires OuterClass$InnerClass(?x);
    //@ ensures OuterClass$InnerClass(x) &*& result == x;
  {
    //@ open OuterClass$InnerClass(x);
    return this.x;
  }
    
  void setX(int i)    
    //@ requires OuterClass$InnerClass(_);
    //@ ensures OuterClass$InnerClass(i);
  {
    x = i;
  }
    
  static int getY()    
   //@ requires OuterClass$InnerClass_y(?y');
   //@ ensures OuterClass$InnerClass_y(y') &*& result == y'; 
  {
    return y;
  }
    
  static void setY(int i)    
    //@ requires OuterClass$InnerClass_y(_);
    //@ ensures OuterClass$InnerClass_y(i);
  {
    y = i;
  }
}
