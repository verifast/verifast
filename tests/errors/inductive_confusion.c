/*@

fixpoint t my_default_value<t>();

inductive unit1 = unit1;
inductive unit2 = unit2;

lemma void absurd()
    requires true;
    ensures false; //~ should_fail
{
    switch (my_default_value<unit1>) { case unit1: }
    switch (my_default_value<unit2>) { case unit2: }
}

@*/
