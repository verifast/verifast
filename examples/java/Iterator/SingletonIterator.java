package iterator.singleton;

import iterator.it.*;

public class SingletonIterator implements Iterator {

    Object value;
    boolean done;
    
    /*@
    
    predicate valid(list<Object> elements) =
        value |-> ?v &*& v != null &*& done |-> ?d &*&
        d ? elements == nil : elements == cons(v, nil);
    
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
        //@ requires valid(?ys);
        //@ ensures valid(ys) &*& result == (ys != nil);
    {
        //@ open valid(ys);
        boolean result = !this.done;
        //@ close valid(ys);
        return result;
    }
    
    public Object next()
        //@ requires valid(?ys) &*& ys != nil;
        //@ ensures valid(tail(ys)) &*& result == head(ys) &*& result != null;
    {
        //@ open valid(ys);
        this.done = true;
        Object result = this.value;
        //@ close valid(nil);
        return result;
    }

}
