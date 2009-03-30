interface Iterator {
  boolean hasNext();
      //@ requires iterator(this.getClass())(this, ?ys);
      //@ ensures iterator(this.getClass())(this, ys) &*& result==(ys!=nil);

  Object next();
      //@ requires iterator(this.getClass())(this, ?xs) &*& xs!=nil;
      //@ ensures switch (xs) { case nil: return false; case cons(x, xs0): return iterator(this.getClass())(this, xs0) &*& result == x &*& x!=null; };
}
