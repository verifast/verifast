/*@

lemma void foo(int y, int z)
    requires z == (y <= mydiv2(1) ? 0 : 1);
    ensures false;
{
}

@*/
