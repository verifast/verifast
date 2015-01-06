//@ #include "nat.gh"

/*@

lemma void induction(nat n, nat m)
  requires true;
  ensures  true;
{
  switch(n)
  {
    case succ(n0):
      induction(n, m); //~
    case zero:
  }
}

@*/