#include "stdlib.h"

/*@

inductive foo<t> = foo(t);

inductive bar = bar(foo<bar>);  //~ should_fail

lemma void ouch(bar b)
    requires true;
    ensures false;
{
    switch (b) {
        case bar(f):
            switch (f) {
                case foo(b0):
                    ouch(b0);
            }
    }
}

@*/

struct frob {
    int x;
    //@ bar b;
};

int main()
    //@ requires true;
    //@ ensures true;
{
    struct frob *f = malloc(sizeof(struct frob));
    if (f == 0) abort();
    //@ ouch(f->b);
    assert(false);
}
