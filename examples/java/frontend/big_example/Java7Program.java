// This example Java 7 program illustrates the support added to VeriFast
// as part of the STANCE EU project for many Java 7 features, including:
// - generics
// - anonymous inner classes
// - varargs (variable-length argument lists)
// - boxing and unboxing of primitive types
// - enhanced for loops (a.k.a. foreach loops)
// This support is enabled through VeriFast's use of the STANCE Java frontend,
// which is derived from OpenJDK.
//
// Furthermore, the example illustrates VeriFast's support for the following Java features:
// - classes
// - interfaces
// - arrays
// - class methods that implement interface methods
// - checked and unchecked exceptions
// - Java Collections API usage, including types List and Iterator

package mypackage;

import java.util.*;

/*@

fixpoint int sum(list<int> l){
   switch(l) {
     case nil : return 0;
     case cons(i, r) : return i + sum(r);
   }
}

fixpoint list<b> map<a, b> (fixpoint(a, b) f, list<a> l){
  switch(l){
    case nil : return nil;
    case cons (x, r) : return cons(f (x), map(f, r));
  }
}

predicate_family FoldFunc(Class c)(FoldFunc f, list<Object> in, Object acc, any info);

@*/

interface FoldFunc<A, T> 
{    
  T fold(T x0, A x1);  
    //@ requires FoldFunc(this.getClass())(this, cons(x1, ?r), x0, ?info);
    //@ ensures FoldFunc(this.getClass())(this, r, result, info);
}

class EmptyException extends Exception 
{
}

/*@
  
predicate_family_instance FoldFunc(Java7Program$1.class)(FoldFunc f, list<Integer> in, Integer acc, list<Integer> info) =
         not_null(in) == true &*& acc != null &*&
         sum(map(Integer_intValue, info)) == sum(map(Integer_intValue, in)) + Integer_intValue(acc); 
  
@*/

public class Java7Program
{
  public static <T> void addAll(List<T> l, T... xs) throws EmptyException /*@ ensures xs.length == 0; @*/
    //@ requires l.List(?l_es) &*& [?f]xs[..] |-> ?xs_es;
    //@ ensures l.List(append(l_es, xs_es)) &*& [f]xs[..] |-> xs_es &*& xs.length > 0;
  {
    if (xs.length > 0)
    {
      List<T> temp = Arrays.asList(xs);
      //@ close listIsCollection(temp, temp);
      l.addAll(temp);
    }
    else
    {
      throw new EmptyException();
    }
  }
  
  public static <A, T> T fold(FoldFunc<A, T> f, List<A> xs, T acc0)
    //@ requires xs.List(?es) &*& FoldFunc(f.getClass())(f, es, acc0, ?info) &*& f != null;
    //@ ensures xs.List(es) &*& FoldFunc(f.getClass())(f, nil, result, info);
  {
    T acc = acc0;
    
    //@ xs.listToIterable();
    for (A x : xs) 
      //@ requires i$.Iterator((seq_of_list)(es), _, ?n) &*& FoldFunc(f.getClass())(f, drop(n, es), acc, info) &*& f != null &*& n >= 0 &*& n <= length(es);
      //@ ensures FoldFunc(f.getClass())(f, nil, acc, info) &*& i$.Iterator((seq_of_list)(es), _, length(es));
    {
      //@ drop_n_plus_one(n, es);
      acc = f.fold(acc, x);
    }
    //@ xs.destroyIterator();
    //@ xs.iterableToList();
    
    return acc;
  }
  
  public static void main(String... args)
    //@ requires true;
    //@ ensures true;
  {
    List<Integer> xs = new ArrayList<Integer>();
    Integer i1 = 3;
    Integer i2 = 5;
    Integer i3 = 7;

    try
    {
      addAll(xs, i1, i2, i3);
    }
    catch (EmptyException e)
    {
      //@ assert false;
    }
    
    //@ list<Integer> exs = {i1, i2, i3};
    
    FoldFunc func = new FoldFunc<Integer, Integer>() 
    {
      public Integer fold(Integer x0, Integer x1) 
        //@ requires FoldFunc(Java7Program$1.class)(this, cons(x1, ?r), x0, ?info);
        //@ ensures FoldFunc(Java7Program$1.class)(this, r, result, info);
      { 
        //@ open FoldFunc(Java7Program$1.class)(this, cons(?_o, ?_r), x0, ?_info);
        Integer res = x0 + x1;
        return res;
         //@ close FoldFunc(Java7Program$1.class)(this, _r, res, _info);
      }
    }; 
    Integer acc = 2;
    //@ close FoldFunc(Java7Program$1.class)(func, exs, acc, cons(acc, exs));
    Integer vi = fold(func, xs, acc);
    //@ open FoldFunc(Java7Program$1.class)(_, _, _, _);
    int v = vi;
    
    //@ assert v == 17;
    
    //@ boolean is_thrown = false;
    try
    {
      addAll(xs);
    }
    catch (EmptyException e)
    {
      //@ is_thrown = true;
    }
    //@ assert is_thrown;
    
    Object i = null;
    //@ is_thrown = false;
    try
    {
      if (i == null)
        throw new NullPointerException();
      else
      {}
    }
    catch (NullPointerException e)
    {
      //@ is_thrown = true;
    }
    //@ assert is_thrown;
  }
}
