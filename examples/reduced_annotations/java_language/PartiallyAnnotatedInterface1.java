class NotAnnotatedInterface1_1
{
  private int x; 

  NotAnnotatedInterface1_1(int i) {/*@ assert false; @*/x = i;}

  int NotAnnotatedInterface1_1_1(int i) {/*@ assert false; @*/return i;}
}

public interface PartiallyAnnotatedInterface1
{
  public int annotatedIncInterface1_1(int i);
    //@ requires i < 100;
    //@ ensures result == i + 1;

  public int NotAnnotatedIncInterface1(int i);

  public int annotatedIncInterface1_2(int i);
    //@ requires i < 100;
    //@ ensures result == i + 1;
}

class NotAnnotatedInterface1_3
{
  private int x; 

  NotAnnotatedInterface1_3(int i) {/*@ assert false; @*/x = i;}

  int NotAnnotatedInterface1_3_1(int i) {/*@ assert false; @*/return i;}
}