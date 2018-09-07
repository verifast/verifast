/*@

lemma void mult_test(real a, real b, real c)
    requires a == b * c;
    ensures
        b == 0 ? a == b * c &*& a == 0 :
        b == 1 ? a == b * c &*& a == c :
        b == 2 ? a == b * c &*& a == 2*c :
        c == 0 ? a == b * c &*& a == 0 :
        c == 1 ? a == b * c &*& a == b :
        c == 2 ? a == b * c &*& a == 2*b :
        true;
{
}

@*/
