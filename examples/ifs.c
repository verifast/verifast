bool random();
    //@ requires true;
    //@ ensures true;

int main()
    //@ requires true;
    //@ ensures true;
{
    bool r = true;
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}

    //@ invariant true;

    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    r = random();
    if (r) {} else {}
    return 0;
}
