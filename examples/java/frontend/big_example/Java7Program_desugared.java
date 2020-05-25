package mypackage;

import java.util.*;

/*@

fixpoint int sumize(list<int> l){
   switch(l) {
     case nil : return 0;
     case cons(i, r) : return i + sumize(r);
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

interface FoldFunc
{    
  Object fold(Object acc, Object x);   
    //@ requires FoldFunc(this.getClass())(this, cons(?o, ?r), acc, ?info) &*& o == x;
    //@ ensures FoldFunc(this.getClass())(this, r, result, info);
}

class EmptyException extends Exception 
{
}

/*@
  
predicate_family_instance FoldFunc(Java7Program_desugared$1.class)(FoldFunc f, list<Integer> in, Integer acc, list<Integer> info) =
         not_null(in) == true &*& acc != null &*&
         sumize(map(Integer_intValue, info)) == sumize(map(Integer_intValue, in)) + Integer_intValue(acc); 
  
@*/

public class Java7Program_desugared 
{
  public static <T> void addAll(List<T> l, T[] xs) throws EmptyException /*@ ensures xs.length == 0; @*/
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

  public static <T> T fold(FoldFunc f, List<T> xs, T acc0)
    //@ requires xs.List(?es) &*& FoldFunc(f.getClass())(f, es, acc0, ?info) &*& f != null;
    //@ ensures xs.List(es) &*& FoldFunc(f.getClass())(f, nil, result, info);
  {
    T acc = acc0;
    
    //@ xs.listToIterable();
    {
      Iterator<T> iSSS = xs.iterator();
      while (iSSS.hasNext())
        //@ requires iSSS.Iterator((seq_of_list)(es), _, ?n) &*& FoldFunc(f.getClass())(f, drop(n, es), acc, info) &*& f != null &*& n >= 0 &*& n <= length(es);
        //@ ensures FoldFunc(f.getClass())(f, nil, acc, info) &*& iSSS.Iterator((seq_of_list)(es), _, length(es));
      {
        T x = iSSS.next();
        {
          //@ drop_n_plus_one(n, es);
          acc = f.fold(acc, x);
        }
      }
    }
    //@ xs.destroyIterator();
    //@ xs.iterableToList();
    
    return acc;
  } 

  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    List<Integer> xs = new ArrayList<Integer>(); 
    Integer i1 = Integer.valueOf(3);
    Integer i2 = Integer.valueOf(5);
    Integer i3 = Integer.valueOf(7);
    
    try
    {
      Java7Program_desugared.<Integer>addAll(xs, new Integer[]{i1, i2, i3});
    }
    catch (EmptyException e)
    {
      //@ assert false;
    }
    //@ list<Integer> exs = {i1, i2, i3};
    
    FoldFunc func = new Java7Program_desugared$1();
    Integer acc = Integer.valueOf(2);
    //@ close FoldFunc(Java7Program_desugared$1.class)(func, exs, acc, cons(acc, exs));
    Integer vi = Java7Program_desugared.<Integer>fold(func, xs, acc);
    //@ open FoldFunc(Java7Program_desugared$1.class)(_, _, _, _);
    int v = vi.intValue();
    
    //@ assert v == 17;
    
    //@ boolean is_thrown = false;
    try
    {
      Java7Program_desugared.<Integer>addAll(xs, new Integer[]{});
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

class Java7Program_desugared$1 implements FoldFunc 
{
  public Integer fold(Integer acc, Integer x)
    //@ requires FoldFunc(Java7Program_desugared$1.class)(this, cons(?o, ?r), acc, ?info) &*& o == x;
    //@ ensures FoldFunc(Java7Program_desugared$1.class)(this, r, result, info);
  {
    //@ open FoldFunc(Java7Program_desugared$1.class)(this, cons(?_o, ?_r), acc, ?_info);
    Integer res = Integer.valueOf(acc.intValue() + x.intValue());
    return res;
    //@ close FoldFunc(Java7Program_desugared$1.class)(this, _r, res, _info);
  }  

  public Object fold(Object x0, Object x1)
    //@ requires FoldFunc(Java7Program_desugared$1.class)(this, cons(?o, ?r), x0, ?info) &*& o == x1;
    //@ ensures FoldFunc(Java7Program_desugared$1.class)(this, r, result, info);
  {
    return this.fold((Integer) x0, (Integer) x1);
  }
}


