package subpackage;

//@ predicate predicate1() = true;

interface Interface1
{
}

//@ fixpoint int fixpoint1(int i) {return i;}

public class Subpackage implements Interface1
{
}

/*@

lemma void lemma1()
  requires true;
  ensures true;
{
  assert true;
}

@*/

