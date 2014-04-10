class OuterClass
{
  class InnerClass
  {
    //@ predicate OuterClass$InnerClass(int x) = this.x |-> x;
    
    int x = 1;
    
    InnerClass()
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
  }
}

public class MemberClass
{
  public static void main(String[] args)
    //@ requires class_init_token(OuterClass$InnerClass.class);
    //@ ensures true; 
  {
    //@ init_class(OuterClass$InnerClass.class);
    
    OuterClass first = new OuterClass();
    OuterClass.InnerClass second = first.new InnerClass();
    
    //Non-static stuff
    second.setX(111);
    int i = second.getX();
    //@ assert i == 111;
 }
}
