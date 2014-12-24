//@ #include "mylib.gh"
//@ #include "yourlib.gh"

int main() //@ : main
     //@ requires true;
     //@ ensures true;
{
     //@ length_zero_eq_nil(nil);
     //@ length_not_zero_not_nil(cons(0, nil));
     return 0;
}
