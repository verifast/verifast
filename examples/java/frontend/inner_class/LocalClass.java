public class LocalClass
{
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true; 
  {
    class InnerClass
    {
      //@ predicate LocalClass$InnerClass(int x) = this.x |-> x;
      
      int x = 1;
      
      InnerClass()
      //@ requires true;
      //@ ensures  LocalClass$InnerClass(1);
      {
        //@ close LocalClass$InnerClass(1);
      }
        
      int getX()    
        //@ requires LocalClass$InnerClass(?x);
        //@ ensures LocalClass$InnerClass(x) &*& result == x;
      {
        //@ open LocalClass$InnerClass(x);
        return this.x;
      }
        
      void setX(int i)    
        //@ requires LocalClass$InnerClass(_);
        //@ ensures LocalClass$InnerClass(i);
      {
        x = i;
      }
    }  
  
    InnerClass first = new InnerClass();
    
    //Non-static stuff
    first.setX(111);
    int i = first.getX();
    //@ assert i == 111;
 }
}