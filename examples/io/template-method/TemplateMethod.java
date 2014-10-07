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
predicate_family m1_io(Class c)(any t1; any t2);
predicate_family m2_io(Class c)(any t1; any t2);
@*/

/**
 * Class that does a "complex" (here simplified since it's an example) calculation,
 * but delegates some steps to the subclass.
 */
public abstract class ComplexCalculation {
  // predicate body is unused - subclasses can choose whatever representation they want.
  //@ predicate time(any x) = x == default_value<any> &*& false;

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
}


/*@
predicate_family_instance m1_io(Adder)(adder_time t1, adder_time t2) =
  t1 == adder_time(?value)
  &*& value == Short.MAX_VALUE ?
    t2 == t1
  :
    t2 == adder_time(value + 1)
;
predicate_family_instance m2_io(Adder)(adder_time t1, adder_time t2) =
  t1 == adder_time(?value)
  &*& value > Short.MAX_VALUE - 20 ?
    t2 == t1
  :
    t2 == adder_time(value + 20)
;
inductive adder_time = adder_time(int value);
@*/
/**
 * Class that does a calculation, by adding a number.
 */
public class Adder extends ComplexCalculation {
  short x = 0;
  //@ predicate time(any t1) = this->x |-> ?x &*& t1 == adder_time(x);

  public Adder()
    //@ requires true;
    //@ ensures time(adder_time(0));
  {
  }

  public void m1()
    //@ requires time(?t1) &*& m1_io(Adder.class)(t1, ?t2);
    //@ ensures time(t2);
  {
    //@ open time(t1);
    //@ open m1_io(Adder.class)(_, _);
    if (x != Short.MAX_VALUE){
      x = (short)(x + 1);
    }
    //@ close time(t2);
  }
  
  public void m2()
    //@ requires time(?t1) &*& m2_io(Adder.class )(t1, ?t2);
    //@ ensures time(t2);
  {
    //@ open time(t1);
    //@ open m2_io(Adder.class)(_, _);
    if (x <= Short.MAX_VALUE - 20){
      x = (short)(x + 20);
    }
    //@ close time(t2);
  }
  
  public int getValue()
    //@ requires time(?t) &*& t == adder_time(?v);
    //@ ensures time(t) &*& result == v;
  {
    return x;
  }
}

/*@
predicate_family_instance m1_io(Multiplier)(multiplier_time t1, multiplier_time t2) =
  t1 == multiplier_time(?x)
  &*& x * 2 > Integer.MAX_VALUE ? // Would cause integer overflow
    t2 == t1
  :
    t2 == multiplier_time(x * 2)
;
predicate_family_instance m2_io(Multiplier)(multiplier_time t1, multiplier_time t2) = 
  t1 == multiplier_time(?x)
  &*& x * 3 > Integer.MAX_VALUE ? // Would cause integer overflow
    t2 == t1
  :
    t2 == multiplier_time(x * 3)
;

inductive multiplier_time = multiplier_time(int x);
@*/


/**
 * Class that does a calculation, by multiplying a number.
 */
public class Multiplier extends ComplexCalculation {
  int value = 1; // It is possible to have a different representation.
  /*@
  predicate time(any t) =
    this.value |-> ?value
    &*& value >= 0
    &*& t == multiplier_time(value);
  @*/
  
  public Multiplier()
  //@ requires true;
  //@ ensures time(multiplier_time(1));
  {
  }

  public void m1()
    //@ requires time(?t1) &*& m1_io(Multiplier.class)(t1, ?t2);
    //@ ensures time(t2);
  {
    //@ open time(t1);
    //@ open m1_io(Multiplier.class)(_, _);
    if (value <= Integer.MAX_VALUE / 2){
      value = value * 2;
    }
    //@ close time(t2);
  } 
  
  public void m2()
    //@ requires time(?t1) &*& m2_io(Multiplier.class)(t1, ?t2);
    //@ ensures time(t2);
  {
    //@ open time(t1);
    //@ open m2_io(Multiplier.class)(_, _);
    if (value <= Integer.MAX_VALUE / 3){
      value = value * 3;
    }
    //@ close time(t2);
  } 
  
  public int getValue()
    //@ requires time(?t);
    //@ ensures time(t) &*& t == multiplier_time(?x) &*& result == x;
  {
    return value;
  }
}

public class Test {
  public static void main(String[] args)
  //@ requires true;
  //@ ensures true;
  {
    Adder calc1 = new Adder();
    //@ close m1_io(Adder.class)(adder_time(0), ?t2);
    //@ close m1_io(Adder.class)(t2, ?t3);
    //@ close m2_io(Adder.class)(t3, ?t4);
    calc1.template();
    int should_be_22 = calc1.getValue();
     assert should_be_22 == 22;
    // Or a ghost assert: (both are statically checked by VeriFast)
    //@ assert should_be_22 == 22;
    
    Multiplier calc2 = new Multiplier();
    //@ assert calc2.time(?calc2_t1);
    //@ close m1_io(Multiplier.class)(multiplier_time(1), ?calc2_t2);
    //@ close m1_io(Multiplier.class)(calc2_t2, ?calc2_t3);
    //@ close m2_io(Multiplier.class)(calc2_t3, ?calc2_t4);
    calc2.template();
    int should_be_12 = calc2.getValue();
    assert should_be_12 == 12;
    
  }
}



