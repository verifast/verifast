int myfunction3(int* b, int len)
//@ requires b[0..len] |-> ?p &*& forall_(int i; (i>0 && i<len)?nth(i, p)>0:true);
//@ ensures b[0..len] |-> p &*& result > 0;
{
  if (len >= 2)
    return b[1];
  else
    return 1;
}
