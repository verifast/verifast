//@ predicate module(int moduleId, bool initialized) = false;

int main() //@ : main_full(prelude_redef)
    //@ requires module(prelude_redef, true);
    //@ ensures false;
{
    //@ open module(_, _);
    return 0; //~allow_dead_code
}
