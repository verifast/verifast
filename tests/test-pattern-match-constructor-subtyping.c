/*@

inductive my_ind = my_ind(int x);

predicate helper(my_ind my_ind);
predicate accept_any(any my_ind) =
  my_ind == my_ind(?z); // No type error.
  

// You can use this to see if the error message is correct
// Correct: "Type mismatch. Actual: my_ind2. Expected: my_ind." (1)
// Incorrect: "Type mismatch. Actual: my_ind. Expected: my_ind2." (2)
//inductive my_ind2 = my_ind2(int x);
//predicate test(my_ind ind) = ind == my_ind2(_);


// If the typechecking is reversed (thus (2) instead of (1)),
// you can still workaround it as follows:
predicate helper(my_ind my_ind);
predicate accept_any_(any my_ind) =
  helper(?my_ind_cp)
  &*& my_ind == my_ind_cp;
@*/

