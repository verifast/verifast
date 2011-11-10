Team members:
Bart Jacobs <bart.jacobs@cs.kuleuven.be>
Jan Smans <jan.smans@cs.kuleuven.be>
Dries Vanoverberghe <Dries.Vanoverberghe@cs.kuleuven.be>
Willem Penninckx <willem.penninckx@cs.kuleuven.be>

Programs have been verified using VeriFast: http://people.cs.kuleuven.be/~bart.jacobs/verifast/

Problem 1
---------
The specification of two_way_sort proves the following properties:
  1. safety (no array indexing errors)
  2. termination (via loop decreases: j - i + 1)
  3. behavior 
    (a) the resulting array is sorted (postcondition: is_sorted(vs2))
    (b) the resulting array is a permutation of the original array (postcondition: is_perm(vs, vs2))

Problem 2
---------
The specification in problem2.java proves all required properties:
  1. the method reduction correctly reduces the term and the resulting term cannot be reduced any further
  2. if the term contains no S subterms, then reduction terminates 
  3. proven parity lemma (even -> K, odd -> KK)
  
see problem2.java for more comments

caveat: 
 - 1 trivial assume related to natural numbers (nat_le_not_eq): \forall x: nat, y: nat :: x < y  ==> x <= y - 1

Alternative, cleaner verified implementation in values/Combinators.java.

Problem 3
---------
The solution implements and verifies all functions (create, clear, head, push,
pop) and the test harness. Verified properties include safety, behavior,
and absence of integer overflow.
To verify, open in vfide and press F5.
The lemma tail_of_singleton_is_nil is currently unverified.

Alternative, cleaner verified implementation in problem3_alt.c.

Problem 4: Tree Reconstruction
------------------------------
- Fully implemented purely (in annotations) and in C.
- Verified that pure implementation is sound and complete. VeriFast also checks that it terminates.
- Verified compliance of C implementation with pure implementation.
- Verified test harness (pure and in C).
- VeriFast does not check termination of C code.

Problem 5: Breadth-first search
-------------------------------
- Fully implemented in C
- Big verified library of lemmas about pure sets as lists.
- Verified that if bfs succeeds, there exists a path of returned length. (Not: minimal path; not: completeness.)
- Specification of full soundness and completeness (in comments), but not verified.
(- No harness.)
