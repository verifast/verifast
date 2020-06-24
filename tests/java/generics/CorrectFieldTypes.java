import java.util.*;

public class GenericClass<T> {
    public T t;
	
    public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    {
        GenericClass<Integer> gi = new GenericClass< >();
        Integer i = gi.t;
        ArrayList<Integer> arrayInt = new ArrayList< >();
        Foo<Integer> fooI = new Foo< >();
        ArrayList<Integer> ai = fooI.t;
    }
}

class Foo<U> extends GenericClass<ArrayList<U> > {}

