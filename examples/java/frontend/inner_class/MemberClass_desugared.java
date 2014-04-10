class OuterClass 
{
}

public class MemberClass_desugared
{
  public static void main(String[] args)    
    //@ requires class_init_token(OuterClass$InnerClass.class);
    //@ ensures true; 
  {
    //@ init_class(OuterClass$InnerClass.class);

    OuterClass first = new OuterClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass(first /**Null check is missing*/);
    second.setX(111);
    int i = second.getX();
    /*@ assert i == 111;@*/
  }
}

class OuterClass$InnerClass 
{
  final OuterClass this$0;
  
  //@ predicate OuterClass$InnerClass(int x) = this.x |-> x;
  
  int x = 1;
    
  OuterClass$InnerClass(OuterClass this$0)    
    //@ requires true;
    //@ ensures  OuterClass$InnerClass(1); 
  {
    super();
    this.this$0 = this$0;
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
}
