/*@
lemma void foo(real x)
    requires true;
    ensures x - 2*x/5 == 3*x/5;
{
}
@*/

int main() //@ : main
   //@ requires true;
   //@ ensures true;
{
   //@ real x = 2/5;
   //@ assert 1 - x == 3/5;
   return 0;
}