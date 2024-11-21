void emptyWhileBody()
//@ requires true;
//@ ensures true;
{
  while (true)
    //@ invariant true;
    ;
}

void nonCompoundWhileBody(int &i)
//@ requires integer(&i, ?v);
//@ ensures integer(&i, ?k) &*& k >= 10 &*& k >= v;
{
  while (i < 10)
    //@ invariant integer(&i, ?iv) &*& iv >= v;
    ++i;
}

int nonCompoundIfElseBody(int &i)
//@ requires integer(&i, ?v);
//@ ensures integer(&i, v);
{
  if (i < 10)
    return 0;
  else
    return 1;
}

int main()
//@ requires true;
//@ ensures true;
{
  int i = 0;
  //@ integer_limits(&i);
  emptyWhileBody();
  nonCompoundWhileBody(i);
  nonCompoundIfElseBody(i);
}