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

public class HelloWorld 
{
  public <T> void genericFunction(T argument){}
  public static GenericClass<GenericClass<Foo> > genericInstance;
  
  public static void main(String[] args) 
    //@ requires System_out(?o) &*& o != null;
    //@ ensures true; 
  {
    System.out.println("Hello, World");
    GenericClass<String> list = new GenericClass<String>("fo");
    list.add("hello");
    String s = list.get();   // no cast
  }
}
