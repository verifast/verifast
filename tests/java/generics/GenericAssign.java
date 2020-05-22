class B<E>{}
class Bar<T> extends B<Integer>{}
class Foo<T> extends B<Boolean>{}

public class GenericAssign{

    public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    {
        B<Integer> bint = new B< >();
        Bar<Boolean> barbool = new Bar< >();
        Foo<Boolean> foobool = new Foo< >();

        bint = barbool;
        bint = foobool; //~
    }
}