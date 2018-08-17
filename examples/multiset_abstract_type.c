/*@

abstract_type multiset; // Finite multiset of integers.

fixpoint int multiset_size(multiset M);

fixpoint int multiset_multiplicity(multiset M, int element);

fixpoint multiset multiset_empty();

fixpoint multiset multiset_insert(multiset M, int element);

lemma_auto void multiset_size_empty();
    requires true;
    ensures multiset_size(multiset_empty) == 0;

lemma_auto void multiset_multiplicity_empty(int x);
    requires true;
    ensures multiset_multiplicity(multiset_empty, x) == 0;

lemma void multiset_size_insert(multiset M, int x);
    requires true;
    ensures multiset_size(multiset_insert(M, x)) == multiset_size(M) + 1;

lemma void multiset_multiplicity_insert(multiset M, int x, int y);
    requires true;
    ensures multiset_multiplicity(multiset_insert(M, x), y) == (x == y ? multiset_multiplicity(M, x) + 1 : multiset_multiplicity(M, y));

@*/
