//@ #include "nat.gh"

/*@

lemma void induction(nat n1, nat n2, nat n3)
  requires true;
  ensures  true;
{
  induction(n1, n2, n3); //~
}

@*/