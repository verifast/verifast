package iterator.it;

public interface Iterator {

    //@ predicate valid(list<Object> elements);
    
    boolean hasNext();
        //@ requires valid(?xs);
        //@ ensures valid(xs) &*& result == (xs != nil);
        
    Object next();
        //@ requires valid(?xs) &*& xs!=nil;
        //@ ensures valid(tail(xs)) &*& result == head(xs) &*& result != null;

}
