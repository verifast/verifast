enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  enum day d = monday;
  //@ assert d == 0;
  //@ assert sunday == 6;
  d = 35;
  int x = d;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}


