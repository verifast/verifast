// verifast_annotation_char:#

public class AnnotationChar
{
  public static void test()
    //# requires true;
    //# ensures true;
  {
    int i = 0;
    //# assert i == 0;
    //@ assert false;
    i++;
    //# assert i == 1;
  }
}