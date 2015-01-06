//@ #include "nat.gh"

/*@

lemma void induction(nat n1, nat n2)
  requires true;
  ensures  true;
{
  switch(n1)
  {
    case succ(n10):
      switch(n2)
      {
        case succ(n20):
          induction(n20, n10); //~
        case zero:
      }
    case zero:
  }
}

@*/