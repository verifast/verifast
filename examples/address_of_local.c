// doesn't verify yet

void inc(int* i)
  //@ requires integer(i, ?v);
  //@ ensures integer(i, v+1);
{
  (*i) = (*i) + 1;
}

void inc_char(char* i)
  //@ requires character(i, ?v);
  //@ ensures character(i, (char)(v+1));
{
  (*i) = (char) ((*i) + 1);
}

bool myfunc() 
  //@ requires true;
  //@ ensures result == true;
{
  return true;
}

void address_of_param(int x) 
  //@ requires true;
  //@ ensures true;
{
    x = 5;
    int* ptr = &x; 
    inc(ptr);
    int z = x;
    assert(z == 6);
}

void address_of_param2(char* x) 
  //@ requires character(x, ?v);
  //@ ensures character(x, (char)(v + 1));
{
    char** ptr = &x; 
    char y = *x;
    inc_char(*ptr);
    int z = *x;
    assert(z == y+1);
}