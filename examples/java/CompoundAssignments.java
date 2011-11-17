class CompoundAssignments {
  int f;
  
  void test1() 
    //@ requires true;
    //@ ensures true;
  {
    int x = 0;
    x += (++x) + (++x) + (x+=1);
    //@ assert x == 6;
    int y = 0;
    int z = 0;
    int t = (x = 2) + (y = 3) + (z = 4);
    assert t == 9 && x == 2 && y == 3 && z == 4;
  }
  
  void test2() 
    //@ requires this.f |-> 1;
    //@ ensures this.f |-> 3;
  {
    this.f += ++this.f;
  }
  
  int consumef() 
    //@ requires this.f |-> _;
    //@ ensures result ==  0;
  {
   return 0;
  }
    
  void test3() 
    //@ requires this.f |-> 0;
    //@ ensures true;
  {
    this.f += consumef(); //~ should_fail
  }
}