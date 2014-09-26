
/*@
predicate_family predfam(Class c)(option<boolean> y; option<boolean> z);
@*/

/*@
predicate_family_instance predfam(A)(option<boolean> x, option<boolean> y) = y == none;
predicate_family_instance predfam(B)(option<boolean> x, option<boolean> y) = y == some(true);
@*/
public abstract class A {
  
  public abstract void m();
    // note the (atypical) A.class. z3 gives a type error (crashes VeriFast).
    //@ requires exists<option<boolean > >(?t1) &*& predfam(A.class)(t1, ?t2);
    //@ ensures true;
}


public class B extends A {

  public void m()
    //@ requires exists<option<boolean > >(?t1) &*& predfam(B.class)(t1, ?t2);
    //@ ensures true;
  {
  }   
  
}
