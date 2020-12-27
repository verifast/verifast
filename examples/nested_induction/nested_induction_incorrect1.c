//@ #include "nat.gh"

/*@

lemma void induction(nat n)
  requires true;
  ensures  true;
{
  int i;
  switch(n)
  {
    case succ(n0):
      induction(n0); //~
    case zero:
  }
}

@*/