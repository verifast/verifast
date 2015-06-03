abstract class A {public String toString(){return "A";} }

class B extends A {}

class C extends A {}

final class F extends A {}

/*@
lemma void instance_of_non_final__get_class (A x)
requires x instanceof B;
ensures x.getClass() == B.class;//~
{
}
@*/