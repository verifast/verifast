/*@

lemma void simplex_incompleteness(real ra, real rl, real rx, real rx_rct2)
    requires 
        rl <= ra &*&
        ra == 0 &*&
        0 <= rx &*&
        rx <= rx_rct2 &*&
        rx_rct2 == 0;
    ensures rx == 0;
{
}

@*/
