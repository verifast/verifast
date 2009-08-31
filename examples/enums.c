enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

int main() 
  //@ requires true;
  //@ ensures true;
{
  enum day d = monday;
  //@ assert d == 0;
  //@ assert sunday == 6;
  d = 35;
  int x = d;
  return 0;
}


