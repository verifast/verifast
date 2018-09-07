/*@

lemma void redux_incompleteness(real d, real d2, real ru, real ndru, real rrb)
    requires
        rrb != d &*&
        d <= ndru &*&
        d2 <= d &*&
        rrb <= d &*&
        ru <= d &*&
        rrb <= ndru &*&
        ndru <= rrb;
    ensures false;
{
}

@*/