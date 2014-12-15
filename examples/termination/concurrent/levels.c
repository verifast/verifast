//@ #include "levels.gh"
//@ #include <quantifiers.gh>

/*@

fixpoint real real_of_level(level level) {
    switch (level) {
        case level(r): return r;
    }
}

fixpoint bool real_lt(real r1, real r2) { return r1 < r2; }
fixpoint bool real_gt(real r1, real r2) { return r1 > r2; }

fixpoint real real_min(real r, list<real> rs) {
    switch (rs) {
        case nil: return r;
        case cons(r0, rs0): return real_lt(r0, r) ? real_min(r0, rs0) : real_min(r, rs0);
    }
}

fixpoint real real_max(real r, list<real> rs) {
    switch (rs) {
        case nil: return r;
        case cons(r0, rs0): return real_gt(r0, r) ? real_max(r0, rs0) : real_max(r, rs0);
    }
}

lemma void note(bool b)
    requires b;
    ensures b;
{}

lemma void real_min_le(real r, list<real> rs)
    requires true;
    ensures real_min(r, rs) <= r;
{
    switch (rs) {
        case nil:
        case cons(r0, rs0):
            if (real_lt(r0, r)) {
                real_min_le(r0, rs0);
            } else
                real_min_le(r, rs0);
    }
}

lemma void real_max_ge(real r, list<real> rs)
    requires true;
    ensures real_max(r, rs) >= r;
{
    switch (rs) {
        case nil:
        case cons(r0, rs0):
            if (real_gt(r0, r))
                real_max_ge(r0, rs0);
            else
                real_max_ge(r, rs0);
    }
}

fixpoint bool real_le(real r1, real r2) { return r1 <= r2; }

lemma void forall_real_min_le(real r, list<real> rs)
    requires true;
    ensures forall(rs, (real_le)(real_min(r, rs))) == true;
{
    switch (rs) {
        case nil:
        case cons(r0, rs0):
            if (r0 < r) {
                real_min_le(r0, rs0);
                forall_real_min_le(r0, rs0);
            } else {
                real_min_le(r, rs0);
                forall_real_min_le(r, rs0);
            }
    }
}

lemma void lt_real_min_level_all_above(level l1, real r, list<level> ls)
    requires real_of_level(l1) < real_min(r, map(real_of_level, ls));
    ensures level_all_above(ls, l1) == true;
{
    switch (ls) {
        case nil:
        case cons(l0, ls0):
            assert l1 == level(?r1);
            assert l0 == level(?r0);
            if (real_of_level(l0) < r) {
                real_min_le(r0, map(real_of_level, ls0));
                lt_real_min_level_all_above(l1, real_of_level(l0), ls0);
            } else {
                real_min_le(r, map(real_of_level, ls0));
                lt_real_min_level_all_above(l1, r, ls0);
            }
    }
}

lemma void gt_real_max_level_all_below(level l1, real r, list<level> ls)
    requires real_of_level(l1) > real_max(r, map(real_of_level, ls));
    ensures level_all_below(ls, l1) == true;
{
    switch (ls) {
        case nil:
        case cons(l0, ls0):
            assert l1 == level(?r1);
            assert l0 == level(?r0);
            if (real_gt(real_of_level(l0), r)) {
                real_max_ge(r0, map(real_of_level, ls0));
                gt_real_max_level_all_below(l1, real_of_level(l0), ls0);
            } else {
                real_max_ge(r, map(real_of_level, ls0));
                gt_real_max_level_all_below(l1, r, ls0);
            }
    }
}

lemma void mem_real_min(real r, list<real> rs)
    requires true;
    ensures real_min(r, rs) == r || mem(real_min(r, rs), rs);
{
    switch (rs) {
        case nil:
        case cons(r0, rs0):
            if (r0 < r)
                mem_real_min(r0, rs0);
            else
                mem_real_min(r, rs0);
    }
}

lemma void mem_real_max(real r, list<real> rs)
    requires true;
    ensures real_max(r, rs) == r || mem(real_max(r, rs), rs);
{
    switch (rs) {
        case nil:
        case cons(r0, rs0):
            if (r0 > r)
                mem_real_max(r0, rs0);
            else
                mem_real_max(r, rs0);
    }
}

lemma a mem_map_mem<a, b>(b y, fixpoint(a, b) f, list<a> xs)
    requires mem(y, map(f, xs)) == true;
    ensures mem(result, xs) && f(result) == y;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (f(x) == y) {
                return x;
            } else {
                return mem_map_mem(y, f, xs0);
            }
    }
}

lemma void level_all_above_lt_real_min(level ub, list<level> ubs, level lb)
    requires level_all_above(cons(ub, ubs), lb) == true;
    ensures real_of_level(lb) < real_min(real_of_level(ub), map(real_of_level, ubs));
{
    mem_real_min(real_of_level(ub), map(real_of_level, ubs));
    assert mem(real_min(real_of_level(ub), map(real_of_level, ubs)), map(real_of_level, cons(ub, ubs))) == true;
    level l = mem_map_mem(real_min(real_of_level(ub), map(real_of_level, ubs)), real_of_level, cons(ub, ubs));
    forall_elim(cons(ub, ubs), (level_below)(lb), l);
    assert lb == level(?rlb);
    assert l == level(?rl);
}

lemma void level_all_below_all_real_max_lt_real_min(level lb, list<level> lbs, level ub, list<level> ubs)
    requires level_all_below_all(cons(lb, lbs), cons(ub, ubs)) == true;
    ensures real_max(real_of_level(lb), map(real_of_level, lbs)) < real_min(real_of_level(ub), map(real_of_level, ubs));
{
    mem_real_max(real_of_level(lb), map(real_of_level, lbs));
    level l = mem_map_mem(real_max(real_of_level(lb), map(real_of_level, lbs)), real_of_level, cons(lb, lbs));
    assert l == level(?rl);
    forall_elim(cons(lb, lbs), (level_all_above)(cons(ub, ubs)), l);
    level_all_above_lt_real_min(ub, ubs, l);
}

lemma level create_level(list<level> lowerBounds, list<level> upperBounds)
    requires level_all_below_all(lowerBounds, upperBounds) == true;
    ensures level_all_below(lowerBounds, result) && level_all_above(upperBounds, result);
{
    switch (lowerBounds) {
        case nil:
            switch (upperBounds) {
                case nil:
                    return level(0);
                case cons(ub, ubs):
                    assert ub == level(?rub);
                    level result = level(real_min(rub, map(real_of_level, ubs)) - 1);
                    real_min_le(rub, map(real_of_level, ubs));
                    lt_real_min_level_all_above(result, rub, ubs);
                    return result;
            }
        case cons(lb, lbs):
            assert lb == level(?rlb);
            switch (upperBounds) {
                case nil:
                    level result = level(real_max(rlb, map(real_of_level, lbs)) + 1);
                    real_max_ge(rlb, map(real_of_level, lbs));
                    gt_real_max_level_all_below(result, rlb, lbs);
                    return result;
                case cons(ub, ubs):
                    assert ub == level(?rub);
                    level result = level((real_max(rlb, map(real_of_level, lbs)) + real_min(rub, map(real_of_level, ubs))) / 2);
                    level_all_below_all_real_max_lt_real_min(lb, lbs, ub, ubs);
                    real_max_ge(rlb, map(real_of_level, lbs));
                    gt_real_max_level_all_below(result, rlb, lbs);
                    real_min_le(rub, map(real_of_level, ubs));
                    lt_real_min_level_all_above(result, rub, ubs);
                    return result;
            }
    }
}

lemma void level_below_transitive(level level1, level level2, level level3)
    requires level_below(level1, level2) == true &*& level_below(level2, level3) == true;
    ensures level_below(level1, level3) == true;
{
    assert level1 == level(?r1);
    assert level2 == level(?r2);
    assert level3 == level(?r3);
}

lemma void level_below_antireflexive(level level)
    requires true;
    ensures !level_below(level, level);
{
    assert level == level(?r);
}

@*/