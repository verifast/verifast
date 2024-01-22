/*@

inductive mypair<a, b> = mypair(a fst, b snd);

lemma void test()
    requires true;
    ensures true;
{
    mypair<int, bool> p = mypair(42, true);
    int x = p.fst;
    int y = p.snd;
    p.fst++;
    assert p.fst == 43;
    p.snd = !p.snd;
    assert p.snd == false;
}

@*/
