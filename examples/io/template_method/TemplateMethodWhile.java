/**
 * Like TemplateMethod.java, but the template method is implemented as
 * while (m1()) { m2() }.
 */

/*@
// t1 should not be precise, hence we cannot just use a predicate inside a class.
predicate_family m1_io(Class c)(any t1; boolean result, any t2);
predicate_family m2_io(Class c)(any t1; any t2);
@*/

/*@
predicate template_io(any t1, Class c, any t2) =
  m1_io(c)(t1, ?return_value, ?t_m1)
  &*& return_value ?
    m2_io(c)(t_m1, ?t_m2)
    &*& template_io(t_m2, c, t2)
  :
    t2 == t_m1
  ;
@*/

public abstract class ComplexCalculation {
  //@ predicate token(any x) = x == default_value<any> &*& false;

  public void template()
    /*@ requires this.token(?t1)
      &*& template_io(t1, this.getClass(), ?t2);
    @*/
    //@ ensures this.token(t2);
  {
    //@ open template_io(_, _, _);
    while (m1())
        /*@ invariant
            this.token(?t_cur)
            &*& m1_io(this.getClass())(t_cur, ?return_val, ?t_m1)
            &*& return_val ?
              m2_io(this.getClass())(t_m1, ?t_m2)
              &*& template_io(t_m2, this.getClass(), t2)
            :
              t2 == t_m1;
        @*/
    {
      m2();
      //@ open template_io(_, this.getClass(), t2);
    }
  }
  
  // The paper formalization does only allow expressions as guard for while loops.
  // This version of the template method is written as such.
  public void template_guard_is_expression()
    /*@ requires this.token(?t1)
      &*& template_io(t1, this.getClass(), ?t2);
    @*/
    //@ ensures this.token(t2);
  {
    //@ open template_io(_, _, ?t_open1);
    boolean return_val = m1();
    while (return_val)
        /*@ invariant
          this.token(?t_cur)
          &*& return_val ?
            m2_io(this.getClass())(t_cur, ?t_m2)
            &*& template_io(t_m2, this.getClass(), t2)
          : t2 == t_cur;
        @*/
    {
      m2();
      //@ open template_io(_, this.getClass(), t2);
      return_val = m1();
    }
  }

  public abstract boolean m1();
    //@ requires token(?t1) &*& m1_io(this.getClass())(t1, ?result_value, ?t2);
    //@ ensures token(t2) &*& result == result_value;
  
  public abstract void m2();
    //@ requires token(?t1) &*& m2_io(this.getClass())(t1, ?t2);
    //@ ensures token(t2);
}


// The rest is the same as the TemplateMethod.java file, except that m1 now must
// return a boolean such that it can be used as the while guard.

/*@
predicate_family_instance m1_io(Adder)(adder_place t1, boolean result, adder_place t2) =
  t1 == adder_place(?value)
  &*& value == Short.MAX_VALUE ?
    t2 == t1 &*& result == false
  :
    t2 == adder_place(value + 1) &*& result == true
;
predicate_family_instance m2_io(Adder)(adder_place t1, adder_place t2) =
  t1 == adder_place(?value)
  &*& value > Short.MAX_VALUE - 20 ?
    t2 == t1
  :
    t2 == adder_place(value + 20)
;
inductive adder_place = adder_place(int value);
@*/
/**
 * Class that does a calculation, by adding a number.
 */
public class Adder extends ComplexCalculation {
  short x = 0;
  //@ predicate token(any t1) = this.x |-> ?x &*& t1 == adder_place(x);

  public Adder()
    //@ requires true;
    //@ ensures token(adder_place(0));
  {
  }

  public boolean m1()
    //@ requires token(?t1) &*& m1_io(Adder.class)(t1, ?return_value, ?t2);
    //@ ensures token(t2) &*& result == return_value;
  {
    //@ open token(t1);
    //@ open m1_io(Adder.class)(_, _, _);
    if (x != Short.MAX_VALUE){
      x = (short)(x + 1);
      return true;
    }else{
      return false;
    }
  }
  
  public void m2()
    //@ requires token(?t1) &*& m2_io(Adder.class )(t1, ?t2);
    //@ ensures token(t2);
  {
    //@ open token(t1);
    //@ open m2_io(Adder.class)(_, _);
    if (x <= Short.MAX_VALUE - 20){
      x = (short)(x + 20);
    }
    //@ close token(t2);
  }
  
  public int getValue()
    //@ requires token(?t) &*& exists<int>(?v) &*& t == adder_place(v);
    //@ ensures token(t) &*& result == v;
  {
    return x;
  }
}

/*@
predicate_family_instance m1_io(Multiplier)(multiplier_place t1, boolean result, multiplier_place t2) =
  t1 == multiplier_place(?x)
  &*& x * 2 > Integer.MAX_VALUE ? // Would cause integer overflow
    t2 == t1
    &*& result == false
  :
    t2 == multiplier_place(x * 2)
    &*& result == true
;
predicate_family_instance m2_io(Multiplier)(multiplier_place t1, multiplier_place t2) = 
  t1 == multiplier_place(?x)
  &*& x * 3 > Integer.MAX_VALUE ? // Would cause integer overflow
    t2 == t1
  :
    t2 == multiplier_place(x * 3)
;

inductive multiplier_place = multiplier_place(int x);
@*/


/**
 * Class that does a calculation, by multiplying a number.
 */
public class Multiplier extends ComplexCalculation {
  int value = 1; // It is possible to have a different representation.
  /*@
  predicate token(any t) =
    this.value |-> ?value
    &*& value >= 0
    &*& t == multiplier_place(value);
  @*/
  
  public Multiplier()
  //@ requires true;
  //@ ensures token(multiplier_place(1));
  {
  }

  public boolean m1()
    //@ requires token(?t1) &*& m1_io(Multiplier.class)(t1, ?return_value, ?t2);
    //@ ensures token(t2) &*& result == return_value;
  {
    //@ open token(t1);
    //@ open m1_io(Multiplier.class)(_, _, _);
    if (value <= Integer.MAX_VALUE / 2){
      value = value * 2;
      return true;
    }else{
      return false;
    }
  } 
  
  public void m2()
    //@ requires token(?t1) &*& m2_io(Multiplier.class)(t1, ?t2);
    //@ ensures token(t2);
  {
    //@ open token(t1);
    //@ open m2_io(Multiplier.class)(_, _);
    if (value <= Integer.MAX_VALUE / 3){
      value = value * 3;
    }
    //@ close token(t2);
  } 
  
  public int getValue()
    //@ requires token(?t);
    //@ ensures token(t) &*& exists<int>(?x) &*& t == multiplier_place(x) &*& result == x;
  {
    return value;
    //@ close exists(value);
  }
}

