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

lemma void bitand_bitor_1_2_lemma(void *x)
    requires true == (((uintptr_t)x & 1) == 0);
    ensures  true == ((((uintptr_t)x | 2) & 1) == 0);
{
    uintptr_t ux = (uintptr_t)x;
    Z zx = Z_of_int(ux);
    switch (zx) {
    case Zsign(zxs):
    case Zdigit(zx1, zd0):
        switch (zx1) {
        case Zsign(zxs):
        case Zdigit(zx2, zd1):
        }
    }
    Z z1 = Zdigit(Zsign(false), true);
    Z z2 = Zdigit(Zdigit(Zsign(false), true), false);
    bitand_def(ux, zx, 1, z1);
    bitor_def(ux, zx, 2, z2);
    bitand_def(ux | 2, Z_or(zx, z2), 1, z1);
}

lemma void bitand_plus_4(void *x)
    requires true == (((uintptr_t)x & 1) == 0) &*& true == (((uintptr_t)x & 2) == 0);
    ensures true == (((uintptr_t)(x + 4) & 1) == 0) &*& true == (((uintptr_t)(x + 4) & 2) == 0);
{
    uintptr_t ux = (uintptr_t)x;
    Z zx = Z_of_int(ux);
    switch (zx) {
    case Zsign(zxs):
    case Zdigit(zx1, zd0):
        switch (zx1) {
        case Zsign(zxs):
        case Zdigit(zx2, zd1):
        }
    }
    
    Z z1 = Zdigit(Zsign(false), true);
    Z z2 = Zdigit(Zdigit(Zsign(false), true), false);
    
    uintptr_t uxp4 = (uintptr_t)(x + 4);
    Z zxp4 = Z_of_int(uxp4);
    switch (zxp4) {
    case Zsign(zxp4s):
    case Zdigit(zxp4_1, zxp4_d0):
        switch (zxp4_1) {
        case Zsign(zxp4s):
        case Zdigit(zxp4_2, zxp4_d1):
            switch (zxp4_2) {
            case Zsign(zxp4s):
            case Zdigit(zxp4_3, zxp4_d3):
            }
        }
    }
    
    bitand_def(ux, zx, 1, z1);
    bitand_def(ux, zx, 2, z2);
    bitand_def(uxp4, zxp4, 1, z1);
    bitand_def(uxp4, zxp4, 2, z2);
}

@*/
