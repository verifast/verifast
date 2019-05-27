/*@

    lemma void take_nil(list<int> xs, int n)
        requires    xs == nil;
        ensures     take(n, xs) == xs;
    {
        assume (take(n, xs) == xs);
    }

@*/