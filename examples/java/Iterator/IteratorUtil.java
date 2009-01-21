class IteratorUtil {
  public static Object getLast(Iterator iterator)
      //@ requires iterator(iterator.getClass())(iterator, ?xs);
      //@ ensures iterator(iterator.getClass())(iterator, nil) &*& result == objects_last(xs);
  {
      Object value = null;
      boolean more = iterator.hasNext();
      while (more)
          //@ invariant iterator(iterator.getClass())(iterator, ?ys)&*& more == (ys != nil)&*& objects_last(cons(value,ys)) == objects_last(xs);
      {
          value = iterator.next();
          more = iterator.hasNext();
      }
      return value;
  }
}