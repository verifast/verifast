//@ #include "nat.gh"

/*@

lemma void induction(nat n1, nat n2)
  requires true;
  ensures  true;
{
  switch(n2)
  {
    case succ(n20):
      switch(n1)
      {
        case succ(n10):
          induction(zero, n20);
        case zero:
      }
    case zero:
      switch(n1)
      {
        case succ(n10):
          induction(n10, n2); //~
        case zero:
      }
  }
}

@*/