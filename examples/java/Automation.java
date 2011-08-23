//@ predicate a(boolean x; int y) = x ? b(0, 0, 0, y) : y == 0;
//@ predicate b<t1, t2>(t1 x, t1 y, t2 z1; t2 z2) = x == y ? c<t1, t2>(x, z2) : z2 == z1;
//@ predicate c<tp1, tp2>(tp1 x; tp2 y);

//@ predicate n(;);
//@ predicate p(;) = n();



class Automation {
  void test1() 
    //@ requires a(true, 5);
    //@ ensures true;
  {
    //@ assert c(0, 5);
  }
  
  void test2()
    //@ requires p();
    //@ ensures true;
  {
     //@ assert [1/2]n();
  }
  
  
}