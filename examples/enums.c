enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 2000000000, another_large_number, yaln = -0x7fffffff - 1 };

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  enum day d = monday;
  //@ assert d == 0;
  //@ assert sunday == 6;
  d = 35;
  int x = d;
  assert(large_number == 2000000000);
  assert(another_large_number == 2000000001);
  assert(yaln + 1 == -0x7fffffff);
  return 0;
}


