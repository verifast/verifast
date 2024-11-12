int *return_null();
//@ requires true;
//@ ensures result == 0;

int main()
//@ requires true;
//@ ensures false;
{
  int *i = return_null();
  int &iRef = *i; //~should_fail
}
