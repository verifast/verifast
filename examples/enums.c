enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

enum day next_day(enum day d)
//@ requires 0 <= d && d < 7;
//@ ensures 0 <= result && result < 7;
{
  //@ div_rem_nonneg(d + 1, 7);
  return (d + 1) % 7;
}

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


