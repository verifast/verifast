/*@

lemma void ullong__unique(unsigned long long *p)
    requires [?f]ullong_(p, ?v);
    ensures [f]ullong_(p, v) &*& f <= 1;
{
    if(f > 1) {
        open ullong_(_,_);
        integer___unique(p);
        assert false;
    }
}

lemma void u_llong_integer_unique(unsigned long long *p)
    requires [?f]u_llong_integer(p, ?v);
    ensures [f]u_llong_integer(p, v) &*& f <= 1;
{
    if(f > 1) {
        open u_llong_integer(_,_);
        integer__unique(p);
        assert false;
    }
}


  @*/

