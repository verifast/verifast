//@ #include <bitops.gh>
//@ #include "bitops_ex.gh"

/*@

lemma Z Z_of_int_iter(int x, nat fuel)
    requires abs(x) < int_of_nat(fuel);
    ensures int_of_Z(result) == x;
{
    switch (fuel) {
    case zero:
    case succ(fuel0):
    
        if (x == 0)
            return Zsign(false);
        else if (x == -1)
            return Zsign(true);
        else if (0 <= x) {
            div_rem(x, 2);
            Z z0 = Z_of_int_iter(x / 2, fuel0);
            return Zdigit(z0, x % 2 != 0);
        } else {
            div_rem(x - 1, 2);
            Z z0 = Z_of_int_iter((x - 1) / 2, fuel0);
            return Zdigit(z0, (x - 1) % 2 == 0);
        }
    
    }
}

lemma Z Z_of_int(int x)
    requires true;
    ensures int_of_Z(result) == x;
{
    return Z_of_int_iter(x, nat_of_int(abs(x) + 1));
}

lemma void Z_and_Z_or_lemma(Z x, Z y)
    requires int_of_Z(Z_and(x, y)) == 0;
    ensures int_of_Z(y) == int_of_Z(Z_and(Z_or(x, y), y)) &*& int_of_Z(x) == int_of_Z(Z_and(Z_or(x, y), Z_not(y)));
{
    switch (x) {
    case Zsign(xs):
        switch (y) {
        case Zsign(ys):
        case Zdigit(y0, yd):
            Z_and_Z_or_lemma(x, y0);
        }
    case Zdigit(x0, xd):
        switch (y) {
        case Zsign(ys):
        case Zdigit(y0, yd):
            Z_and_Z_or_lemma(x0, y0);
        }
    }
}

lemma void bitand_bitor_lemma(uintptr_t x, uintptr_t y)
    requires true == ((x & y) == 0);
    ensures y == ((x | y) & y) &*& x == ((x | y) & ~y);
{
    Z zx = Z_of_int(x);
    Z zy = Z_of_int(y);
    bitand_def(x, zx, y, zy);
    Z_and_Z_or_lemma(zx, zy);
    bitor_def(x, zx, y, zy);
    bitand_def(x | y, Z_or(zx, zy), y, zy);
    bitnot_def(y, zy);
    bitand_def(x | y, Z_or(zx, zy), ~y, Z_not(zy));
}

@*/
