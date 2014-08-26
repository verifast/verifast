class NotAnnotatedClassMain_1
{
  private int x; 

  NotAnnotatedClassMain_1(int i) {/*@ assert false; @*/x = i;}

  int NotAnnotatedMethodMain_1_1(int i) {/*@ assert false; @*/return i;}
}

//@ predicate incPredicateMain(int i, int j) = j == i + 1;

public class Main
{
  public static void main(String[] args) 
    //@ requires true;
    //@ ensures true; 
  {
    int i = 1;
    PartiallyAnnotated1 o1 = new PartiallyAnnotated1(0);
    PartiallyAnnotatedInterface1 o1_i = o1;
    PartiallyAnnotated2 o2 = new PartiallyAnnotated2(0);
    PartiallyAnnotatedInterface2 o2_i = o2;
    i = annotatedIncMain(i);
    //@ open incPredicateMain(1,i);
    //@ assert i == 2;
    i = o1.annotatedIncInterface1_1(i);
    //@ assert i == 3;
    i = o1_i.annotatedIncInterface1_2(i);
    //@ assert i == 4;
    i = o1.annotatedIncClass1(i);
    //@ assert i == 5;
    i = o2.annotatedIncInterface2_1(i);
    //@ assert i == 6;
    i = o2_i.annotatedIncInterface2_2(i);
    //@ assert i == 7;
    i = o2.annotatedIncClass2(i);
    //@ assert i == 8;

//     System.out.println("Final value   " + i);
//     i = notAnnotatedIncMain(i);
//     System.out.println("Final value++ " + i);
  }

//   class NotAnnotatedClassMain_2
//   {
//     private int x; 
// 
//     NotAnnotatedClassMain_2(int i) {/*@ assert false; @*/ x = i;}
// 
//     int NotAnnotatedMethodMain_2_1(int i) {/*@ assert false; @*/ return i;}
//   }
  
  int NotAnnotatedMethodMain_1(int i) {return i;}

  static int annotatedIncMain(int i)
  //@ requires i < 100;
  //@ ensures incPredicateMain(i, result);
  {
    //@ close incPredicateMain(i, i + 1);
    return ++i;
  }
  
  static int notAnnotatedIncMain(int i) throws Exception
  {
    //@ assert false;
    PartiallyAnnotatedInterface1 o = new PartiallyAnnotated1();

    for (int j = 0; j < 4; j++)
    {
      System.out.println("Foobar");
    }

    return o.NotAnnotatedIncInterface1(i);
  }
  
  int NotAnnotatedMethodMain_2(int i) throws Exception, RuntimeException {return i;}
}

class NotAnnotatedClassMain_3 
{
  private int x; 

  NotAnnotatedClassMain_3(int i) {/*@ assert false; @*/ x = i;}

  int NotAnnotatedMethodMain_3_1(int i) {/*@ assert false; @*/return i;}
}
