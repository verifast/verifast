//@ predicate eq0(any a; any b) = b == a;
//@ predicate eq(any a; unit u) = eq0(a, u); //~ should_fail

//@ inductive color = blue | green;

int main()
    //@ requires true;
    //@ ensures false;
{
    //@ close eq0(blue, blue);
    //@ assert eq(blue, ?u1);
    //@ close eq0(green, green);
    //@ assert eq(green, ?u2);
    //@ switch (u1) { case unit: switch (u2) { case unit: } }
    assert(false);
}