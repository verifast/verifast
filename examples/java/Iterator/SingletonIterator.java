class SingletonIterator implements Iterator {
  Object value;
  boolean done;

  public SingletonIterator(Object value)
      //@ requires value!=null;
      //@ ensures iterator(SingletonIterator.class)(result, cons(value, nil))&*& result.getClass()==SingletonIterator.class;
  {
      this.value = value;
      this.done = false;
      //@ close iterator(SingletonIterator.class)(this, cons(value, nil));
  }
  public boolean hasNext()
  {
      //@ open iterator(SingletonIterator.class)(this, ys);
      boolean result = !this.done;
      //@ close iterator(SingletonIterator.class)(this, ys);
      return result;
  }
  public Object next()
  {
      //@ open iterator(SingletonIterator.class)(this, xs);
      this.done = true;
      Object result = this.value;
      //@ close iterator(SingletonIterator.class)(this, nil);
      return result;
  }
}
