public class MethodInference{
	public static void main(String[] args)
	//@requires true;
	//@ensures true;
	{
		Boolean a = new Boolean(false);
		Integer b = new Integer(3);
		Integer c = new Integer(5);
		Object o = infer(a,b,c);
		Integer o1 = infer(b,b,c);
		
		Integer[] arr = {new Integer(1), new Integer(2), new Integer(3)};
		Integer[] infarr = infer (arr, arr, arr);
		
		Foo<Integer> fi = new Foo< >();
		Foo<Boolean> fb = new Foo< >();
		Foo<Foo<Boolean> > fnested = new Foo< >();
		Object res = infer(fi,fb,fi);
		Foo<Integer> resi = infer(fi,fi,fi);
		
		Foo<Foo<Boolean> > nestedRes = infer (fnested, fnested, fnested);
		Object resnested = infer (fnested, fi, fi);
		
		Bar<Boolean> bar = new Bar< >();
		Foo<Integer> shoul = infer (bar, fi, fi);
	}
	
	public static <T> T infer(T arg1, T arg2, T arg3)
	//@requires true;
	//@ensures true;
	{
        	return arg1;
	}
}

public class Foo<T>{
	
}

public class Bar<T> extends Foo<Integer>{

}