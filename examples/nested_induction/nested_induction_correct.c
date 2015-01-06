//@ #include "nat.gh"

/*@

fixpoint nat nat_10()
{
  return succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(zero))))))))));
}

//Induction on 1 parameter n
lemma void induction1_0(nat n)
  requires true;
  ensures  true;
{
  switch(n)
  {
    case succ(n0):
      induction1_0(n0);
    case zero:
  }
}

//Induction on 1 parameter n with two irrelevant arguments x1 and x2
lemma void induction1_2_1(nat x1, nat n, nat x2)
  requires true;
  ensures  true;
{
  switch(n)
  {
    case succ(n0):
      induction1_2_1(x1, n0, x2);
    case zero:
  }
}

//Induction on 1 parameter n with two irrelevant arguments x1 and x2
lemma void induction1_2_2(nat x1, nat x2, nat n)
  requires true;
  ensures  true;
{
  switch(n)
  {
    case succ(n0):
      induction1_2_2(x1, x2, n0);
    case zero:
  }
}

//Nested induction on 2 parameters n1 and n2
lemma void induction2_0_1(nat n1, nat n2)
  requires true;
  ensures  true;
{
  switch(n1)
  {
    case succ(n10):
      switch(n2)
      {
        case succ(n20):
          //subterm in first argument
          induction2_0_1(n10, n2);
          //subterm in second argument
          induction2_0_1(n10, n20);
          //subterm in second argument
          induction2_0_1(n1, n20);
        case zero:
      }
    case zero:
      switch(n2)
      {
        case succ(n20):
          //subterm in second argument
          induction2_0_1(n1, n20);
        case zero:
      }
  }
}

//Nested induction on 2 parameters n1 and n2 with two irrelevant arguments x1 and x2
lemma void induction2_0_2(nat n1, nat n2, nat x1, nat x2)
  requires true;
  ensures  true;
{
  switch(n1)
  {
    case succ(n10):
      switch(n2)
      {
        case succ(n20):
          //subterm in first argument
          induction2_0_1(n10, n2);
          //subterm in second argument
          induction2_0_1(n10, n20);
          //subterm in second argument
          induction2_0_1(n1, n20);
        case zero:
      }
    case zero:
      switch(n2)
      {
        case succ(n20):
          //subterm in second argument
          induction2_0_1(n1, n20);
          //subterm in second argument
          induction2_0_1(n2, n20);
          //subterm in second argument
          induction2_0_1(zero, n20);
          //subterm in second argument
          induction2_0_1(nat_10, n20);
        case zero:
      }
  }
}

//Nested induction on 3 parameters n1 and n2 with two irrelevant arguments x1 and x2
lemma void induction3(nat n1, nat n2, nat n3, nat x1, nat x2)
  requires true;
  ensures  true;
{
  switch(n1)
  {
    case succ(n10):
      switch(n2)
      {
        case succ(n20):
          switch(n3)
          {
            case succ(n30):
              //subterm in first argument
              induction3(n10, n2, n3, x1, nat_10);
              induction3(n10, nat_10, n3, x1, nat_10);
              //subterm in second argument
              induction3(n1, n20, nat_10, x1, zero);
              induction3(n1, n20, nat_10, zero, x2);
              //subterm in third argument
              induction3(n1, n2, n30, x1, zero);
              induction3(n1, n2, n30, nat_10, nat_10);
            case zero:
          }
        case zero:
      }
    case zero:
  }
}

@*/
