class NotAnnotatedInterface2_1
{
  private int x; 

  NotAnnotatedInterface2_1(int i) {/*@ assert false; @*/x = i;}

  int NotAnnotatedInterface2_1_1(int i) {/*@ assert false; @*/return i;}
}

public interface PartiallyAnnotatedInterface2
{
  public int annotatedIncInterface2_1(int i);
    //@ requires i < 100;
    //@ ensures result == i + 1;

//   class NotAnnotatedInterface2_2
//   {
//     private int x; 
// 
//     NotAnnotatedInterface2_2(int i) {/*@ assert false; @*/x = i;}
// 
//     int NotAnnotatedInterface2_2_1(int i) {/*@ assert false; @*/return i;}
//   }

  public int NotAnnotatedIncInterface2(int i);

  public int annotatedIncInterface2_2(int i);
    //@ requires i < 100;
    //@ ensures result == i + 1;
}

class NotAnnotatedInterface2_3
{
  private int x; 

  NotAnnotatedInterface2_3(int i) {/*@ assert false; @*/x = i;}

  int NotAnnotatedInterface2_3_1(int i) {/*@ assert false; @*/return i;}
}
