struct container{
  int *y;
};

/*@
predicate test_try_use_output_argument_as_lhs_of_pointsto(int some_y; struct container **c) =
  c |-> ?c_deref //~ should fail
;
@*/