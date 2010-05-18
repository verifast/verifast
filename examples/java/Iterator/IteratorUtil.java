package iterator.itutil;

import iterator.it.*;

public class IteratorUtil {

    public static Object getLast(Iterator iterator)
        //@ requires iterator != null &*& iterator.valid(?xs);
        //@ ensures iterator.valid(nil) &*& result == objects_last(xs);
    {
        Object value = null;
        boolean more = iterator.hasNext();
        while (more)
            //@ invariant iterator.valid(?ys) &*& more == (ys != nil) &*& objects_last(cons(value,ys)) == objects_last(xs);
        {
            value = iterator.next();
            more = iterator.hasNext();
            //@ switch (ys) { case nil: case cons(y, ys0): }
        }
        return value;
    }

}
