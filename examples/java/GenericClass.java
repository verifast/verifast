public class GenericClass<T>{
	public T field;
	public GenericClass(T f){
		field = f;
	}
}

public class Foo {}

public class HelloWorld 
{
  public static GenericClass<Foo> genericInstance;
  
  public static void main(String[] args) 
    //@ requires System_out(?o) &*& o != null;
    //@ ensures true; 
  {
    System.out.println("Hello, World");
  }
}
