void foo(bool a, bool b, bool c)
    requires !(a == b) &*& true == (a ? c : true);
    ensures c; //~ should_fail
{
}