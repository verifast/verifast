package iterator.singleton;

import iterator.it.*;
import iterator.itutil.*;

public class SingletonIterator implements Iterator {
  Object value;
  boolean done;

  public SingletonIterator(Object value)
      //@ requires value!=null;
      //@ ensures iterator(SingletonIterator.class)(this, cons(value, nil));
  {
      this.value = value;
      this.done = false;
      //@ close iterator(SingletonIterator.class)(this, cons(value, nil));
  }
  public boolean hasNext()
      //@ requires iterator(SingletonIterator.class)(this, ?ys);
      //@ ensures iterator(SingletonIterator.class)(this, ys) &*& result == (ys != nil);
  {
      //@ open iterator(SingletonIterator.class)(this, ys);
      boolean result = !this.done;
      //@ close iterator(SingletonIterator.class)(this, ys);
      return result;
  }
  public Object next()
      //@ requires iterator(SingletonIterator.class)(this, ?ys) &*& ys != nil;
      //@ ensures iterator(SingletonIterator.class)(this, tail(ys)) &*& result == head(ys) &*& result != null;
  {
      //@ open iterator(SingletonIterator.class)(this, ys);
      this.done = true;
      Object result = this.value;
      //@ close iterator(SingletonIterator.class)(this, nil);
      return result;
  }
}
