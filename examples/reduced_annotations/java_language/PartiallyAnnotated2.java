class NotAnnotatedClass2_1
{
  private int x; 

  NotAnnotatedClass2_1(int i) {/*@ assert false; @*/x = i;}

  int NotAnnotatedClass2_1_1(int i) {/*@ assert false; @*/return i;}
}

public class PartiallyAnnotated2 implements PartiallyAnnotatedInterface2
{
  //@ predicate PartiallyAnnotatedClassPred2(int value) = this.i |-> value;
  
  private int i;
  
  public PartiallyAnnotated2()
  {
    this.i = 0;
  }
  
  public PartiallyAnnotated2(int i)
    //@ requires true;
    //@ ensures  PartiallyAnnotatedClassPred2(i);
  {
    this.i = i;
    //@ close PartiallyAnnotatedClassPred2(i);
  }
  
  public int annotatedIncInterface2_1(int i)
    //@ requires i < 100;
    //@ ensures result == i + 1;
  {
    return ++i;
  }

//   class NotAnnotatedClass2_2
//   {
//     private int x; 
// 
//     NotAnnotatedClass2_2(int i) {/*@ assert false; @*/x = i;}
// 
//     int NotAnnotatedClass2_2_1(int i) {/*@ assert false; @*/return i;}
//   }

  public int NotAnnotatedIncInterface2(int i) 
  {
    //@ assert false;
    return ++i;
  }

  public int annotatedIncInterface2_2(int i)
    //@ requires i < 100;
    //@ ensures result == i + 1;
  {
    return ++i;
  }
  
  public int annotatedIncClass2(int i)
    //@ requires i < 100;
    //@ ensures result == i + 1;
  {
    return ++i;
  }
}

class NotAnnotatedClass2_3
{
  private int x; 

  NotAnnotatedClass2_3(int i) {/*@ assert false; @*/x = i;}

  int NotAnnotatedClass2_3_1(int i) {/*@ assert false; @*/return i;}
}
