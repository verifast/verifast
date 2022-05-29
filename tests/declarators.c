void test(char *a1, char *a2, char **a3)
  //@ requires true;
  //@ ensures true;
{
  char *p1 = a1, *p2 = a2, **p3 = a3;
} 
