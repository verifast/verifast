import subpackage.Subpackage;
//@ import subpackage.predicate1;
//@ import subpackage.lemma1;

class Main 
{
  public static void main(String[] args) 
    //@ requires true;
    //@ ensures true; 
  {
    Subpackage o = new Subpackage();
    /*~*/ //@ int i = fixpoint1(0);
  }
}
