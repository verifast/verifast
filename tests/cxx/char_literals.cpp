int main()
    //@ requires true;
    //@ ensures true;
{
    char const val1 = 'd';
    //@ assert val1 == 100;
    char const val2 = u8'f';
    //@ assert val2 == 102;
    unsigned const val3 = u'\405'; // True type is char16_t
    //@ assert val3 == 261;
    unsigned long const val4 = U'\x1D11E'; // True type is char32_t
    //@ assert val4 == 119070;

    char const val5 = '\n';
    //@ assert val5 == 10;
}