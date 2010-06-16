/*@

fixpoint int f(unit u) {
    switch(u) {
        case unit: return (f)(unit) + 1;  //~ should_fail
    }
}

@*/

void m()
  //@ requires true;
  //@ ensures true;
{
  //@ assert false;
}
