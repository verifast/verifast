class C {
  final static int f = 10;
  
  void m()
    //@ requires true;
    //@ ensures true;
  {
    short x = 20 + f;
    //@ assert x == 30;
  }
}