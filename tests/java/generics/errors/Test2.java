class B<E>{}
class Bar<T> extends B<Integer>{}
class Foo<T> extends B<Boolean>{}

public class Test2{
    
    public void test2()
    //@ requires true;
    //@ ensures true;
    {
    	B<Integer> bint = new B< >();
    	Foo<Boolean> foobool = new Foo< >();
    	bint = foobool; //~
    }
}