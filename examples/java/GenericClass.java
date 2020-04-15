import java.util.ArrayList;
import java.util.List;

public class GenericClass<T>{
	public T field;
	public GenericClass(T f)
	//@ requires true;
	//@ ensures this.field |-> f;
	{
		field = f;
	}
	
	public void add(T arg)
	//@ requires this.field |-> ?f;
	//@ ensures this.field |-> arg;
	{
		field = arg;
	}
	
	public T get()
	//@ requires this.field |-> ?f;
	//@ ensures this.field |-> f;
	{
		return field;
	}
}

public class Foo {}

/*
	Proper method overrides
*/
// Case A: Interface implements interface
public interface Parent<A,B>{
	public A get1(A arg1);
	public B get2();
}

public interface Child<C,D> extends Parent<D,C>{
	public D get1(D arg1);
	public C get2();
}
// Case B: Class implements interface
public class ChildClass<C,D> implements Parent<D,C>{
	public D get1(D arg1) {return null;}
	public C get2() {return null;}
}

// Case C: Class extends class
public abstract class AbstractParentClass<A,B> {
	public abstract A get1(A arg1);
}
public class ChildClassInheritance<C,D> extends AbstractParentClass<C,D>{
	public C get1(C arg1){return null;}
}

public class HelloWorld 
{
  public static <T,V> void genericFunction(T argument, V other)
  //@ requires true;
  //@ ensures true;
  {}
  public static GenericClass<GenericClass<Foo> > genericInstance;
  
  public static void main(String[] args) 
    //@ requires System_out(?o) &*& o != null;
    //@ ensures true; 
  {
    System.out.println("Hello, World");
    GenericClass<GenericClass<String> > list = new GenericClass<GenericClass<String> >(new GenericClass<String>("foo"));
    list.add(new GenericClass<String>("hello"));
    GenericClass<String> s = list.get();   // no cast
    genericFunction<GenericClass<String>,String >(list, "Foo");
    genericFunction< >(list, "Foo");
  }
}
