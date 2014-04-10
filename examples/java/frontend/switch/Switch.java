public class Switch
{
  public static void main(String[] args) 
    //@ requires true;
    //@ ensures  true;
  {
    int day = 4;
    
    int i = 0;
    switch (day) 
    {
      case 1:  i = 1;
               break;
      case 2:  i = 10;
               break;
      case 3:  i = 100;
               break;
      case 4:  i = 1000;
               break;
      default: i = 0;
               break;
    }
    
    //@ assert i == 1000;
  }
}
