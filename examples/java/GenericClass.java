import java.util.ArrayList;
import java.util.List;

public class GenericClass<T>{
	public T field;
	public GenericClass(T f){
		field = f;
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
    GenericClass<String> list = new GenericClass<String>();
    list.add("hello");
    String s = list.get(0);   // no cast
  }
}
