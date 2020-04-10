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
