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