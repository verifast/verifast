interface iX {
}

interface iA extends iX {
}

abstract class A implements iA {
  public int intRep(){
    return 10;
  }
  
  public String StringRep(){
    return "A";
  }
}

class B extends A {}

class C extends A {}

class E extends C {}

final class F extends A {}

class main{
  public static void test(A x, A y)
    //@ requires x != null &*& y != null;
    //@ ensures true;
  {
    A tst = null;
    if (x instanceof C){
      if(x instanceof B){
        //@ assert false;
        //tst.StringRep();
      }
    }
    if (x instanceof E){
      if (!(x instanceof C)){
        //@ assert false;
        //tst.StringRep();
      }
      if (!(x instanceof iA)){
        //@ assert false;
        //tst.StringRep();
      }
    }
    B u = new B();
    if (!(u instanceof iX)){
       //@ assert false;
       //u.intRep();
    }
    //@produce_instanceof(x);
    if(!(x instanceof iA)){
      //@ assert false;
      //x.intRep();
    }
    //@ A w = y;
    //@produce_instanceof(w);
    /*@
    if(!(w instanceof iA)){
      assert false;
      //y.intRep();
    } @*/
  }
}

/*@
lemma void instance_of_final__get_class (A x)
requires x instanceof F;
ensures x.getClass() == F.class;
{
}
@*/
