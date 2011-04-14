package iterator;

interface Iterator {

    //@ predicate valid(list<Object> xs);
    
    boolean hasNext();
        //@ requires valid(?xs);
        //@ ensures valid(xs) &*& result == (xs != nil);

    Object next();
        //@ requires valid(?xs) &*& xs != nil;
        //@ ensures valid(tail(xs)) &*& result == head(xs) &*& result != null;

}

/*@

fixpoint Object objects_last(list<Object> a) {
    switch (a) {
        case nil: return null;
        case cons(x, xs): return x != null && xs == nil ? x : objects_last(xs);
    }
}

@*/

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    /*@
    
    predicate valid(list<Object> xs) =
        value |-> ?v &*& v != null &*& done |-> ?d &*& d ? xs == nil : xs == cons(v, nil);
    
    @*/
    
    public SingletonIterator(Object value)
        //@ requires value != null;
        //@ ensures valid(cons(value, nil));
    {
        this.value = value;
        this.done = false;
        //@ close valid(cons(value, nil));
    }
    
    public boolean hasNext()
        //@ requires valid(?xs);
        //@ ensures valid(xs) &*& result == (xs != nil);
    {
        //@ open valid(xs);
        return !done;
        //@ close valid(xs);
    }
    
    public Object next()
        //@ requires valid(?xs) &*& xs != nil;
        //@ ensures valid(tail(xs)) &*& result == head(xs) &*& result != null;
    {
        //@ open valid(xs);
        done = true;
        return value;
        //@ close valid(nil);
    }

}

class IteratorUtil {

    public static Object getLast(Iterator iterator)
        //@ requires iterator.valid(?xs);
        //@ ensures iterator.valid(nil) &*& result == objects_last(xs);
    {
        Object value = null;
        boolean more = iterator.hasNext();
        while (more)
            //@ invariant iterator.valid(?ys) &*& more == (ys != nil) &*& objects_last(cons(value, ys)) == objects_last(xs);
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
        Object o = new Object();
        SingletonIterator i = new SingletonIterator(o);
        boolean before = i.hasNext();
        assert(before);

        Object last = IteratorUtil.getLast(i);
        assert last == o;
      
        boolean after = i.hasNext();
        assert(!after);
    }

}