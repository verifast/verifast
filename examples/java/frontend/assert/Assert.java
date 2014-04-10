public class Assert
{
  public static void main(String[] args)
    //@ requires true;
    //@ ensures  true;
  {
    int i = 99;
    assert (i > 0);
    assert i > 0;
    char c = 'a';
    assert (c + 4 == 'e');
    assert c + 4 == 'e' : "foobar";
  }
}