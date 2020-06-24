public class GenericClass<T> {
    public T t;

    public GenericClass(T value)
    //@ requires true;
    //@ ensures this.t |-> value;
    {
        t = value;
    }

    public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    {
        GenericClass<Integer> gi = new GenericClass< >(new Integer(5));
        Integer i = gi.t;
    }
}

