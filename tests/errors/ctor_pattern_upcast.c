/*@

inductive color = blue | red;
inductive wrapped_unit = wrapped_unit(unit u);

lemma void absurd()
    requires true;
    ensures false;
{
    any c1 = blue;
    any c2 = red;
    assert c1 == wrapped_unit(?u1); //~should_fail
    //switch (u1) { case unit: }
    //assert c2 == wrapped_unit(?u2);
    //switch (u2) { case unit: }
}

@*/
