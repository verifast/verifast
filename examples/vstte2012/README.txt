
Team members:
Bart Jacobs <bart.jacobs@cs.kuleuven.be>
Jan Smans <jan.smans@cs.kuleuven.be>
Dries Vanoverberghe <Dries.Vanoverberghe@cs.kuleuven.be>
Willem Penninckx <willem.penninckx@cs.kuleuven.be>

VeriFast (and vfide) is available for free from
http://people.cs.kuleuven.be/~bart.jacobs/verifast/


Problem 3
---------
The solution implements and verifies all functions (create, clear, head, push,
pop) and the test harness. Verified properties include safety, behavior,
and absence of integer overflow.
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
