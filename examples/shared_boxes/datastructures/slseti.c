
//@ #include "slseti.gh"

/*@

// relation with lset_contains (for other lemma's, use slset_*)

lemma void slseti_add_contains(list<int> s, int v, int v2)
    requires true;
    ensures lset_contains(slseti_add(s, v), v2) == (v == v2 || lset_contains(s, v2));
{
    slset_add_contains(s, v, v2, intlt);
}

lemma void slseti_remove_contains(list<int> s, int el, int el2)
    requires isSlseti(s) == true;
    ensures lset_contains(slseti_remove(s, el), el2) == (el != el2 && lset_contains(s, el2));
{
    produce_lemma_function_pointer_chunk(intlttrans) : lttrans<int>(intlt)(arg1, arg2, arg3) { call(); } 
    {
        assert is_lttrans(?lem1, intlt);
        produce_lemma_function_pointer_chunk(intltirrefl) : ltirrefl<int>(intlt)(arg) { call(); } 
        {
            assert is_ltirrefl(?lem2, intlt);
            slset_remove_contains(s, el, el2, intlt, lem1, lem2);
        }
    }
}

lemma void slseti_union_contains(list<int> s1, list<int> s2, int el)
    requires true;
    ensures lset_contains(slseti_union(s1, s2), el) == (lset_contains(s1, el) || lset_contains(s2, el));
{
    slset_union_contains(s1, s2, el, intlt);
}


// operations maintain isSlseti

lemma void slseti_empty_isSlset()
    requires true; 
    ensures isSlseti(slseti_empty()) == true;
{
}

lemma void slseti_add_isSlset(list<int> s, int v)
    requires isSlseti(s) == true;
    ensures isSlseti(slseti_add(s, v)) == true;
{
    produce_lemma_function_pointer_chunk(intlttotal) : lttotal<int>(intlt)(arg1, arg2) { call(); } 
    {
        assert is_lttotal(?lem1, intlt);
        slset_add_isSlset(s, v, intlt, lem1);
    }
}

lemma void slseti_remove_isSlset(list<int> s, int el)
    requires isSlseti(s) == true;
    ensures isSlseti(slseti_remove(s, el)) == true;
{
    produce_lemma_function_pointer_chunk(intlttrans) : lttrans<int>(intlt)(arg1, arg2, arg3) { call(); } 
    {
        assert is_lttrans(?lem1, intlt);
        slset_remove_isSlset(s, el, intlt, lem1);
    }
}

lemma void slseti_singleton_isSlset(int v)
    requires true;
    ensures isSlseti(slset_singleton(v)) == true;
{
}

lemma void slseti_union_isSlset(list<int> s1, list<int> s2)
    requires isSlseti(s1) == true;
    ensures isSlseti(slseti_union(s1, s2)) == true;
{
    produce_lemma_function_pointer_chunk(intlttotal) : lttotal<int>(intlt)(arg1, arg2) { call(); } 
    {
        assert is_lttotal(?lem1, intlt);
        slset_union_isSlset(s1, s2, intlt, lem1);
    }
}

lemma void slseti_inters_isSlset(list<int> s1, list<int> s2)
    requires isSlseti(s1) == true;
    ensures isSlseti(slseti_inters(s1, s2)) == true;
{
    produce_lemma_function_pointer_chunk(intlttrans) : lttrans<int>(intlt)(arg1, arg2, arg3) { call(); } 
    {
        assert is_lttrans(?lem1, intlt);
        slset_inters_isSlset(s1, s2, intlt, lem1);
    }
}

lemma void slseti_diff_isSlseti(list<int> s1, list<int> s2)
    requires isSlseti(s1) == true;
    ensures isSlseti(slseti_diff(s1, s2)) == true;
{
    produce_lemma_function_pointer_chunk(intlttrans) : lttrans<int>(intlt)(arg1, arg2, arg3) { call(); } 
    {
        assert is_lttrans(?lem1, intlt);
        slset_diff_isSlset(s1, s2, intlt, lem1);
    }
}

// slset is dlset

lemma void slseti_isDlset(list<int> s)
    requires isSlseti(s) == true;
    ensures isDlset(s) == true;
{
    produce_lemma_function_pointer_chunk(intlttrans) : lttrans<int>(intlt)(arg1, arg2, arg3) { call(); } 
    {
        assert is_lttrans(?lem1, intlt);
        produce_lemma_function_pointer_chunk(intltirrefl) : ltirrefl<int>(intlt)(arg) { call(); } 
        {
            assert is_ltirrefl(?lem2, intlt);
            slset_isDlset(s, intlt, lem1, lem2);
        }
    }
}

@*/
