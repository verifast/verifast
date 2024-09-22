#include "pred_confusion.h"

/*@

predicate foo_post() = false;

lemma void absurd()
    requires true;
    ensures false;
{
    foo();
    open foo_post(); //~should_fail
}

@*/
