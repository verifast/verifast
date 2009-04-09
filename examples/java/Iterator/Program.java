package program;
/*@
import iterator.it.iterator;
import iterator.it.objects_last;
@*/
import iterator.it.Iterator;
import iterator.util.IteratorUtil;
import iterator.singleton.SingletonIterator;

class Program {
  public static void main(String[] args)
      //@ requires true;
      //@ ensures true;
  {
      Object o=new Object();
      Iterator i=new SingletonIterator(o);
      boolean before=i.hasNext();
      assert(before);

      Object last = IteratorUtil.getLast(i);
      assert last == o;
      
      boolean after=i.hasNext();
      assert(!after);
  }
}