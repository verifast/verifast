class B<E>{}
class Bar<T> extends B<Integer>{}
class Foo<T> extends B<Boolean>{}

public class Test1{

    public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    {
        B<Integer> bint = new B< >();
        Bar<Boolean> barbool = new Bar< >();
        Foo<Boolean> foobool = new Foo< >();

        bint = barbool;
    }
    
    public void test1()
    //@ requires true;
    //@ ensures true;
    {
    	B<Integer> bint = new B< >();
        B<Object> bobj = new B< >();
        bobj = bint; //~
    }
}