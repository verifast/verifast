/*@

inductive DEFPRED = | TRUE | FALSE;

fixpoint int EQ(DEFPRED TRUE, DEFPRED FALSE) {
  switch (TRUE) {
    case TRUE: return 0;
	case FALSE: return 1;
  }
}

@*/

int blah()
  //@ requires true;
  //@ ensures true;
{
	return 0;
}

void main(int result2)
  //@ requires true;
  //@ ensures true;
{
  int x1 = blah();
  int x2 = blah();
  int x3 = blah();
  int x4 = blah();
  assert (x4 == result2);
  return;
}