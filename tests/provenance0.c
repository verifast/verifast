void provenance()
//@ requires true;
//@ ensures true;
{
  int x[2];
  int y[2];
  // Uncomment the lines below to get VeriFast to accept this program.
  // //@ assume(&x[2] == (int *)(uintptr_t)&x[2]);
  // //@ assume(&y[0] == (int *)(uintptr_t)&y[0]);
  if ((uintptr_t)&x[2] == (uintptr_t)&y[0]) {
    x[2] = 42; //~should_fail
    assert(y[0] == 42); //~allow_dead_code
  }
}
