import java.util.*;

public class Varargs_desugared
{
  public static void addAll(List l,  Object[] xs)
    //@ requires l.List(?l_es) &*& [?f]xs[..] |-> ?l_xs; 
    //@ ensures l.List(append(l_es, l_xs)) &*& [f]xs[..] |-> l_xs; 
  {
    List temp = Arrays.asList(xs);
    //@ close listIsCollection(temp, temp);
    l.addAll(temp);
  }

  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    List l = new ArrayList();
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
  }
}
