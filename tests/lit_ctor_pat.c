//@ predicate foo_(int *p; option<int> v);
//@ predicate foo(int *p; int v) = foo_(p, some(v));
