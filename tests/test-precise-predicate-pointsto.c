// The following code used to crash VeriFast,
// i.e. this is a document-your-commit and anti-regression test.

struct container{
  int *y;
};


struct container *a_global_var;
/*@

predicate test_global_not_precise() =
  a_global_var |-> _
;


predicate test_global_precise(;) =
  a_global_var |-> _
;

@*/