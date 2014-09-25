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
 *
 * In this example, the I/O stye contract of the template method (which 
 * is only written once: in the superclassis) is:
 *  requires this.time(?t1)
 *     &*& m1_io(this.getClass())(t1, ?t2) // This is the calculation that the subclass will perform.
 *     &*& m1_io(this.getClass())(t2, ?t3)
 *     &*& m2_io(this.getClass())(t3, ?t4);
 *  ensures this.time(t4);
 *
 * This expresses: first the behaviour of the method m1 will
 * be performed, then the behaviour of m1 again, and then the behaviour of m2.
 * Multiple subclasses can define different behaviour of their implementation of m1 and m2.
 *
 * Subclasses can choose their own internal data representation.
 */

/*@
// t1 should not be precise, hence we cannot just use a predicate inside a class.
predicate_family m1_io(Class c)(int t1; int t2);
predicate_family m2_io(Class c)(int t1; int t2);
@*/

/**
 * Class that does a "complex" (here simplified since it's an example) calculation,
 * but delegates some steps to the subclass.
 */
public abstract class ComplexCalculation {
  // predicate body is unused - subclasses can choose whatever representation they want.
  //@ predicate time(int x) = x == 0 &*& false;

  /**
   * The template method from the Template Method Design Pattern.
   * 
   * Does a "complex" calculation, delegating some parts to subclasses.
   */
  public void template()
    /*@ requires this.time(?t1)
      &*& m1_io(this.getClass())(t1, ?t2) // This is the calculation that the subclass will perform.
      &*& m1_io(this.getClass())(t2, ?t3)
      &*& m2_io(this.getClass())(t3, ?t4);
    @*/
    //@ ensures this.time(t4);
  {
    // We delegate some steps to subclasses:
    m1();
    m1();
    m2();
  }

  /**
   * Method implemented by subclasses. It does a part of the "complex" calculation.
   */
  public abstract void m1();
    //@ requires time(?t1) &*& m1_io(this.getClass())(t1, ?t2);
    //@ ensures time(t2);
  
  public abstract void m2();
    //@ requires time(?t1) &*& m2_io(this.getClass())(t1, ?t2);
    //@ ensures time(t2);
  
  public abstract int getX();
    //@ requires time(?v);
    //@ ensures time(v) &*& result == v;
}


/*@
predicate_family_instance m1_io(Adder)(int t1, int t2) = t2 == (t1 == Integer.MAX_VALUE ? Integer.MAX_VALUE : t1+1);
predicate_family_instance m2_io(Adder)(int t1, int t2) = t2 == (t1 > Integer.MAX_VALUE - 20 ? Integer.MAX_VALUE : t1+20);
@*/
/**
 * Class that does a calculation, by adding a number.
 */
public class Adder extends ComplexCalculation {
  int x = 0;
  //@ predicate time(int t1) = this.getClass() == Adder.class &*& this->x |-> t1;

  public void m1()
    //@ requires time(?t1) &*& m1_io(this.getClass())(t1, ?t2);
    //@ ensures time(t2);
  {
    //@ open time(t1);
    //@ open m1_io(Adder.class)(_, _);
    if (x != Integer.MAX_VALUE){
      x = x + 1;
    }
    //@ close time(t2);
  }
  
  public void m2()
    //@ requires time(?t1) &*& m2_io(this.getClass())(t1, ?t2);
    //@ ensures time(t2);
  {
    //@ open time(t1);
    //@ open m2_io(Adder.class)(_, _);
    if (x < Integer.MAX_VALUE - 20){
      x = x + 20;
    }else{
      x = Integer.MAX_VALUE;
    }
    //@ close time(t2);
  }
  
  public int getX()
    //@ requires time(?v);
    //@ ensures time(v) &*& result == v;
  {
    return x;
  }
}

/*@
predicate_family_instance m1_io(Multiplier)(int t1, int t2) = t2 == (t1 <= (Integer.MAX_VALUE - 1)/ 2 ? t1 * 2 : Integer.MAX_VALUE);
predicate_family_instance m2_io(Multiplier)(int t1, int t2) = t2 == (t1 <= (Integer.MAX_VALUE - 1)/ 3 ? t1 * 3 : Integer.MAX_VALUE);
@*/
/**
 * Class that does a calculation, by multiplying a number.
 */
public class Multiplier extends ComplexCalculation {
  int myValue = 1;
  //@ predicate time(int x) = this.myValue |-> x &*& x >= 0; // We can also use a totally other representation here.
  
  public Multiplier()
  //@ requires true;
  //@ ensures time(1);
  {
  }

  public void m1()
    //@ requires time(?t1) &*& this.getClass() == Multiplier.class &*& m1_io(this.getClass())(t1, ?t2);
    //@ ensures time(t2);
  {
    //@ open time(t1);
    //@ open m1_io(Multiplier.class)(_, _);
    if (myValue <= Integer.MAX_VALUE / 2){
      myValue = myValue * 2;
    }else{
      myValue = Integer.MAX_VALUE;
    }
    //@ close time(t2);
  } 
  
  public void m2()
    //@ requires time(?t1) &*& this.getClass() == Multiplier.class &*& m2_io(this.getClass())(t1, ?t2);
    //@ ensures time(t2);
  {
    //@ open time(t1);
    //@ open m2_io(Multiplier.class)(_, _);
    if (myValue <= Integer.MAX_VALUE / 3){
      myValue = myValue * 3;
    }else{
      myValue = Integer.MAX_VALUE;
    }
    //@ close time(t2);
  } 
  
  public int getX()
    //@ requires time(?v);
    //@ ensures time(v) &*& result == v;
  {
    return myValue;
  }
}

public class Test {
  public static void main(String[] args)
  //@ requires true;
  //@ ensures true;
  {
    ComplexCalculation calc1 = new Adder();
    //@ assert calc1.time(?t1);
    //@ close m1_io(Adder.class)(t1, ?t2);
    //@ close m1_io(Adder.class)(t2, ?t3);
    //@ close m2_io(Adder.class)(t3, ?t4);
    calc1.template();
    int should_be_22 = calc1.getX();
     assert should_be_22 == 22;
    // Or a ghost assert: (both are statically checked by VeriFast)
    //@ assert should_be_22 == 22;
    
    ComplexCalculation calc2 = new Multiplier();
    //@ assert calc2.time(?calc2_t1);
    //@ close m1_io(Multiplier.class)(calc2_t1, ?calc2_t2);
    //@ close m1_io(Multiplier.class)(calc2_t2, ?calc2_t3);
    //@ close m2_io(Multiplier.class)(calc2_t3, ?calc2_t4);
    calc2.template();
    int should_be_12 = calc2.getX();
    assert should_be_12 == 12;
  }
}

