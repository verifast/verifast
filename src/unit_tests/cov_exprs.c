enum EnumOps {
    ENUM_A = 1 + 2,
    ENUM_B = ENUM_A * 3,
    ENUM_C = ENUM_B - 2,
    ENUM_D = ENUM_C / 2
};

union DataUnion {
    int i;
    char c;
};

struct Point {
    int x;
    int y;
};

/*@
predicate point(struct Point *p; int x, int y) =
    p->x |-> x &*& p->y |-> y;

inductive int_box = int_box(int);
@*/

int helper(int a, int b)
//@ requires true;
//@ ensures result == a + b;
{
    return a + b;
}

void test_all_exprs(struct Point *p, int *arr)
//@ requires point(p, ?px, ?py) &*& arr[0..5] |-> ?elems;
//@ ensures point(p, _, _) &*& arr[0..5] |-> _;
{
    int a = 1;
    int b = 2;
    int c = 3;
    
    p->x;
    arr[0];
    (int)a;
    (a, b);
    a += 1;
    a = b;
    a ? b : c;
    helper(a, b);
    
    switch (a) {
        case 1:
            b = 10;
            break;
        case 2:
            b = 20;
            break;
        default:
            b = 30;
            break;
    }
    
    while (c > 0)
    //@ invariant point(p, _, _) &*& arr[0..5] |-> _ &*& c >= 0;
    {
        c--;
        a = (int)b;
        a += 1;
        p->x = 10;
        p->x += 1;
        arr[0] = 5;
        (a, b);
        a = helper(a, b);
        a = (a ? b : c);
        if (a > 0) {
            b = 1;
        } else {
            b = 2;
        }
        switch (b) {
            case 1:
                b = 2;
                break;
            default:
                b = 3;
                break;
        }
    }
    
    {
        int d = 10;
        int *q = &d;
        *q = 20;
    }
}
