See VSTTE website for what should be in here!!



Problem 3
---------
The solution implements and verifies all functions (create, clear, head, push,
pop) and the test harness. Absence of integer overflow is verified.
To verify, open in vfide and press F5.
The lemma tail_of_singleton_is_nil is currently unverified.

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
