int main()
    //@ requires true;
    //@ ensures true;
{
    { ////    UNSIGNED INT LITERALS    ////
        unsigned const int1 = 0;
        //@ assert int1 == 0;
        unsigned const int2 = 0xFFFFFFFF;
        //@ assert int2 == 4294967295;
        unsigned long long int3 = 0xFFFFFFFFFFFFFFFFull;
        //@ assert int3 == 0xFFFFFFFFFFFFFFFF;
    }

    { ////    SIGNED INT LITERALS    ////
        int const int1 = 0;
        //@ assert int1 == 0;
        int const int2 = -0x7FFFFFFF;
        //@ assert int2 == -2147483647;
        long long int3 = -0x7FFFFFFFFFFFFFFEll;
        --int3;
        //@ assert int3 == -0x7FFFFFFFFFFFFFFF;
    }

    { ////    CHAR LITERALS    ////
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
}