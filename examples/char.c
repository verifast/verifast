int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  char c = 'A';
  //@ assert c == 65;
  return 0;
}