package iterator;

/*@

predicate_family iterator(Class c)(Iterator i, list<Object> xs);

@*/

interface Iterator {
  boolean hasNext();
      //@ requires iterator(this.getClass())(this, ?xs);
      //@ ensures iterator(this.getClass())(this, xs) &*& result == (xs != nil);

  Object next();
      //@ requires iterator(this.getClass())(this, ?xs) &*& xs != nil;
      //@ ensures iterator(this.getClass())(this, tail(xs)) &*& result == head(xs) &*& result != null;
}

/*@
fixpoint Object objects_last(list<Object> a) {
  switch (a) {
      case nil: return null;
      case cons(x, xs): return x!=null && xs == nil ? x : objects_last(xs);
  }
}

@*/

//@ predicate_family_instance iterator(SingletonIterator.class)(SingletonIterator i, list<Object> xs) requires i.value |-> ?value &*& value!=null &*& i.done |-> ?done &*& (done ? xs == nil : xs == cons(value, nil));
class SingletonIterator implements Iterator {
  Object value;
  boolean done;

  public SingletonIterator(Object value)
      //@ requires value!=null;
      //@ ensures iterator(SingletonIterator.class)(result, cons(value, nil));
  {
      this.value = value;
      this.done = false;
      //@ close iterator(SingletonIterator.class)(this, cons(value, nil));
  }
  public boolean hasNext()
      //@ requires iterator(SingletonIterator.class)(this, ?xs);
      //@ ensures iterator(SingletonIterator.class)(this, xs) &*& result == (xs != nil);
  {
      //@ open iterator(SingletonIterator.class)(this, xs);
      boolean result = !this.done;
      //@ close iterator(SingletonIterator.class)(this, xs);
      return result;
  }
  public Object next()
      //@ requires iterator(SingletonIterator.class)(this, ?xs) &*& xs != nil;
      //@ ensures iterator(SingletonIterator.class)(this, tail(xs)) &*& result == head(xs) &*& result != null;
  {
      //@ open iterator(SingletonIterator.class)(this, xs);
      this.done = true;
      Object result = this.value;
      //@ close iterator(SingletonIterator.class)(this, nil);
      return result;
  }
}
class IteratorUtil {
  public static Object getLast(Iterator iterator)
      //@ requires iterator != null &*& iterator(iterator.getClass())(iterator, ?xs);
      //@ ensures iterator(iterator.getClass())(iterator, nil) &*& result == objects_last(xs);
  {
      Object value = null;
      boolean more = iterator.hasNext();
      while (more)
          //@ invariant iterator(iterator.getClass())(iterator, ?ys) &*& more == (ys != nil) &*& objects_last(cons(value, ys)) == objects_last(xs);
      {
          //@ switch (ys) { case nil: case cons(y, ys0): }
          value = iterator.next();
          more = iterator.hasNext();
      }
      return value;
  }
}
class Program {
  public static void main(String[] args)
      //@ requires true;
      //@ ensures true;
  {
      Object o=new Object();
      SingletonIterator i=new SingletonIterator(o);
      boolean before=i.hasNext();
      assert(before);

      Object last = IteratorUtil.getLast(i);
      assert last == o;
      
      boolean after=i.hasNext();
      assert(!after);
  }
}