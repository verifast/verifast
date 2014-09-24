/**
 * This example shows how I/O style contracts can be used for
 * programs that do not perform I/O.
 *
 * In this example, we verify an implementation of the template pattern.
 * In the template pattern, a skeleton of an algorithm is implemented
 * in a method which we call the template methode. The
 * template method delegates some operations to subclasses by calling
 * methods that are overridden by the subclass.
 *
 * We want to define full functional behaviour, i.e. we want to prove
 * that calculations are correct, not only that they do not crash.
 * What are the specifications of the template method? It should state
 * that what the subclass does, is done. How can one specify this, since
 * it is unknown which subclasses there will be?
 *
 * In this example, the template method has an I/O style contract that states
 * that an I/O operation will be executed. The I/O operation is specific
 * to the subclass. This way, the template method's contract is an 
 * easy I/O style contract.
 */

/*@
// t1 should not be precise, hence we cannot just use a predicate inside a class.
predicate_family io(Class c)(int t1; int t2);
@*/

/**
 * Class that does a "complex" (here simplified since it's an example) calculation,
 * but delegates some steps to the subclass.
 */
public abstract class A {
  int x;
  //@ predicate time(int x) = this.x |-> x &*& x > 10;

  public A()
  //@ requires true;
  //@ ensures time(20);
  {
    x = 20;
  }

  /**
   * The template method from the Template Method Design Pattern.
   * 
   * Does a "complex" calculation, delegating some parts to subclasses.
   */
  public void template()
    /*@ requires this.time(?t1)
      &*& io(this.getClass())(t1, ?t2); // This is the calculation that the subclass will perform.
    @*/
    //@ ensures this.time(t2);
  {
    // generic stuff here
    m(); // specific stuff, delegated to subclass
    // more generic stuff here
  }

  /**
   * Method implemented by subclasses. They do a part of the "complex" calculation.
   */
  public abstract void m();
    //@ requires time(?t1) &*& io(this.getClass())(t1, ?t2);
    //@ ensures time(t2);
  
  public int getX()
    //@ requires time(?v);
    //@ ensures time(v) &*& result == v;
  {
    return x;
  }
}


/*@
predicate_family_instance io(AddOne)(int t1, int t2) = t2 == (t1 == Integer.MAX_VALUE ? Integer.MAX_VALUE : t1+1);
@*/
/**
 * Class that does a calculation, by adding one number.
 */
public class AddOne extends A {
  //@ predicate time(int x) = this.getClass() == AddOne.class &*& this.time(A.class)(x);

  public void m()
    //@ requires time(?t1) &*& io(this.getClass())(t1, ?t2);
    //@ ensures time(t2);
  {
    //@ open time(t1);
    //@ assert this.getClass() == AddOne.class;
    //@ open io(AddOne.class)(_, _);
    if (x != Integer.MAX_VALUE){
      x = x + 1;
    }
    //@ close time(t2);
  }
  
  // VeriFast enforces that all methods must be overridden for soundness reasons.
  public int getX()
    //@ requires time(?v);
    //@ ensures time(v) &*& result == v;
  {
    return super.getX();
  }
}

/*@
predicate_family_instance io(TimesTwo)(int t1, int t2) = t2 == (t1 <= Integer.MAX_VALUE / 2 ? t1 * 2 : Integer.MAX_VALUE);
@*/
/**
 * Class that does a calculation, by multiplying the value with two.
 */
public class TimesTwo extends A {
  //@ predicate time(int x) = this.getClass() == TimesTwo.class &*& this.time(A.class)(x);

  public void m()
    //@ requires time(?t1) &*& io(this.getClass())(t1, ?t2);
    //@ ensures time(t2);
  {
    //@ open time(t1);
    //@ open io(TimesTwo.class)(_, _);
    // XXX TODO XXX z3 accepts an "//@ assert false;" here (redux does not). I do not know why.
    ///@ assert false;
    if (x <= Integer.MAX_VALUE / 2){
      x = x * 2;
    }else{
      x = Integer.MAX_VALUE;
    }
    //@ close time(t2);
  } 
  
  // VeriFast enforces that all methods must be overridden for soundness reasons.
  public int getX()
    //@ requires time(?v);
    //@ ensures time(v) &*& result == v;
  {
    return super.getX();
  }
}

public class Test {
  public static void main(String[] args)
  //@ requires true;
  //@ ensures true;
  {
    A a = new AddOne();
    //@ assert a.time(?x);
    //@ close io(AddOne.class)(x, _);
    a.template();
    int should_be_21 = a.getX();
    assert should_be_21 == 21;
    // Or a ghost assert: (both are statically checked by VeriFast)
    //@ assert should_be_21 == 21;
    
    A a2 = new TimesTwo();
    //@ assert a2.time(?x_a2);
    //@ close io(TimesTwo.class)(x_a2, _);
    a2.template();
    int should_be_40 = a2.getX();
    assert should_be_40 == 40;
  }
}

