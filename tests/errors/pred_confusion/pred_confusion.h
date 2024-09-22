#ifndef PRED_CONFUSION
#define PRED_CONFUSION

/*@

predicate_ctor foo_post()() = true;

lemma void foo()
    requires true;
    ensures foo_post();
{
    close foo_post();
}

@*/

#endif PRED_CONFUSION
