import java.util.ArrayList;
import java.util.List;

public class GenericClass<T>{
	public T field;
	public GenericClass(T f)
	//@ requires true;
    	//@ ensures this.field |-> f ; 
	{
		field = f;
	}
	
	public void add(T value) 
	//@ requires true;
    	//@ ensures true; 
    	{
    		field = value;
    	}
	
	public T get()
	//@ requires this.field |-> ?field;
	//@ ensures result == field;
	{
		return field;
	}
}

public class Bar{
	public String field;
	
	public Bar(String f)
	//@ requires true;
    	//@ ensures true; 
	{
		field = f;
	}
	public void add(String value) 
	//@ requires true;
    	//@ ensures true; 
	{
	
	}
}

public class Foo {}

public class HelloWorld 
{
  public <T> void genericFunction(T argument){}
  public static GenericClass<GenericClass<Foo> > genericInstance;
  
  public static void main(String[] args) 
    //@ requires System_out(?o) &*& o != null;
    //@ ensures true; 
  {
    System.out.println("Hello, World");
    Bar b = new Bar("foo");
    b.add("woowee");
    GenericClass<String> gc = new GenericClass<String>("foo");
    gc.add("hello");
    String s = gc.get();   // no cast
  }
}
