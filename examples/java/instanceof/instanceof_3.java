abstract class A {public String toString(){return "A";} }

class B extends A {}

class C extends A {}

interface iA {public String toString(); }

interface iB extends iA {}

interface iC extends iA {}

class main_fail{
  public static void test_fail1(A x)
    //@ requires true;
    //@ ensures true;
  {
    iA tst = null;
    if (x instanceof iC){
      if(x instanceof iB){
        tst.toString(); //~
      }
    }
  }
}