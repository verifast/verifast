class MyException extends Exception {
}

class YourException extends Exception {
}

class Program {

  void test() throws MyException /*@ ensures true; @*/
    //@ requires true;
    //@ ensures false;
  {
    throw new MyException();
  }
  
  void throwsMyException(boolean thrw) throws MyException /*@ ensures thrw == true; @*/
    //@ requires true;
    //@ ensures thrw == false;
  {
    if(thrw) {
      throw new MyException();
    }
  }
  
  void test2() throws YourException /*@ ensures true; @*/
    //@ requires true;
    //@ ensures false;
  {
    try {
      throwsMyException(true);
    } catch(MyException e) {
      throw new YourException();
    }
  }
  
  void test3() throws YourException /*@ ensures true; @*/
    //@ requires true;
    //@ ensures true;
  {
    try {
      throwsMyException(true);
    } catch(MyException e) {
    }
  }
  
  void test4()
    //@ requires true;
    //@ ensures true;
  {
    try {
      throw new MyException();
    } catch(YourException e) {
      assert(false);
    } catch(MyException e) {
    }
  } 
}

class Super {
  void m(int i) throws MyException /*@ ensures true; @*/
    //@ requires true;
    //@ ensures true;
  {
  }
}

class Sub extends Super {
  void m(int i) throws MyException /*@ ensures i == 0; @*/
    //@ requires true;
    //@ ensures true;
  {
  }
}