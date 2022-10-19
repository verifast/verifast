class NotAnnotatedClass1_1
{
  private int x; 

  NotAnnotatedClass1_1(int i) {/*@ assert false; @*/x = i;}

  int NotAnnotatedClass1_1_1(int i) {/*@ assert false; @*/return i;}
}

public class PartiallyAnnotated1 implements PartiallyAnnotatedInterface1
{
  //@ predicate PartiallyAnnotatedClassPred1(int value) = this.i |-> value;
  
  private int i;
  
  public PartiallyAnnotated1()
  {
    this.i = 0;
  }
  
  public PartiallyAnnotated1(int i)
    //@ requires true;
    //@ ensures  PartiallyAnnotatedClassPred1(i);
  {
    this.i = i;
    //@ close PartiallyAnnotatedClassPred1(i);
  }
  
  public int annotatedIncInterface1_1(int i)
    //@ requires i < 100;
    //@ ensures result == i + 1;
  {
    return ++i;
  }

//   class NotAnnotatedClass1_2
//   {
//     private int x; 
// 
//     NotAnnotatedClass1_3(int i) {/*@ assert false; @*/x = i;}
// 
//     int NotAnnotatedClass1_3_1(int i) {/*@ assert false; @*/return i;}
//   }

  public int NotAnnotatedIncInterface1(int i) 
  {
    //@ assert false;
    PartiallyAnnotatedInterface2 o = new PartiallyAnnotated2();
    return o.NotAnnotatedIncInterface2(i);
  }

  public int annotatedIncInterface1_2(int i)
    //@ requires i < 100;
    //@ ensures result == i + 1;
  {
    return ++i;
  }
  
  public int annotatedIncClass1(int i)
    //@ requires i < 100;
    //@ ensures result == i + 1;
  {
    return ++i;
  }
}

class NotAnnotatedClass1_3
{
  private int x; 

  NotAnnotatedClass1_3(int i) {/*@ assert false; @*/x = i;}

  int NotAnnotatedClass1_3_1(int i) {/*@ assert false; @*/return i;}
}
