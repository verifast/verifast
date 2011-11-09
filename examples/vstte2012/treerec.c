//@ #include "nat.h"
//@ #include "listex.h"

/*@

inductive tree = leaf | node(tree, tree);

fixpoint list<int> depths(int d, tree t) {
    switch (t) {
        case leaf: return cons(d, nil);
        case node(l, r): return append(depths(d+1, l), depths(d+1, r));
    }
}

inductive result = success(tree, list<int>) | fail;

fixpoint result build_rec(nat n, int d, list<int> s) {
    switch (n) {
        case zero: return fail;
        case succ(n0): return
            switch (s) {
                 case nil: return fail;
                 case cons(h, s1): return
                     h < d ? fail :
                     h == d ? success(leaf, s1) :
                     switch (build_rec(n0, d+1, s)) {
                         case fail: return fail;
                         case success(l, s2): return
                             switch (build_rec(n0, d+1, s2)) {
                                 case fail: return fail;
                                 case success(r, s3): return
                                     success(node(l, r), s3);
                             };
                     };
            };
   }
}

lemma void harness()
    requires true;
    ensures true;
{
    nat n0 = zero;
    nat n1 = succ(n0);
    nat n2 = succ(n1);
    nat n3 = succ(n2);
    nat n4 = succ(n3);
    
    assert build_rec(n4, 0, cons(1, cons(3, cons(3, cons(2, nil))))) == success(node(leaf, node(node(leaf, leaf), leaf)), nil);
    assert build_rec(n4, 0, cons(1, cons(3, cons(2, cons(2, nil))))) == fail;
}

fixpoint int max_func(int x, int y) { return x < y ? y : x; }

lemma void le_max(int d, list<int> ds)
    requires true;
    ensures d <= fold_left(d, max_func, ds);
{
    switch (ds) {
        case nil:
        case cons(d0, ds0):
            if (d < d0) {
            } else {
            }
            le_max(max_func(d, d0), ds0);
    }
}

lemma void max_le_max(int d1, int d2, list<int> ds)
    requires d1 <= d2;
    ensures fold_left(d1, max_func, ds) <= fold_left(d2, max_func, ds);
{
    switch (ds) {
        case nil:
            
        case cons(d0, ds0):
            max_le_max(max_func(d1, d0), max_func(d2, d0), ds0);
    }
}

lemma void build_rec_sound(nat n, int d, list<int> s)
    requires true;
    ensures
        switch (build_rec(n, d, s)) {
            case fail: return true;
            case success(t, s0): return
                s == append(depths(d, t), s0);
        };
{
    switch (n) {
        case zero:
        case succ(n0):
            switch (s) {
                case nil:
                case cons(h, s1):
                    if (h < d) {
                    } else if (h == d) {
                    } else {
                         build_rec_sound(n0, d+1, s);
                         switch (build_rec(n0, d+1, s)) {
                             case fail:
                             case success(l, s2):
                                 build_rec_sound(n0, d+1, s2);
                                 switch (build_rec(n0, d+1, s2)) {
                                     case fail:
                                     case success(r, s3):
                                         append_assoc(depths(d+1, l), depths(d+1, r), s3);
                                 }
                         }
                     }
             }
    }
}

fixpoint int min_func(int x, int y) { return x < y ? x : y; }

lemma void depths_head(int d, tree t)
    requires true;
    ensures switch (depths(d, t)) { case nil: return false; case cons(dsh, dst): return d <= dsh; };
{
    switch (t) {
        case leaf:
        case node(l, r):
            depths_head(d+1, l);
    }
}

lemma void build_rec_complete(nat n, int d, tree t, list<int> s0)
    requires 0 <= d &*& fold_left(0, max_func, depths(d, t)) < d + int_of_nat(n);
    ensures build_rec(n, d, append(depths(d, t), s0)) == success(t, s0);
{
    switch (n) {
        case zero:
            depths_head(d, t);
            le_max(max_func(d, head(depths(d, t))), tail(depths(d, t)));
            assert d + int_of_nat(n) == d;
        case succ(n0):
            switch (t) {
                case leaf:
                    assert true;
                case node(l, r):
                    depths_head(d+1, l);
                    
                    fold_left_append(0, max_func, depths(d+1, l), depths(d+1, r));
                    le_max(fold_left(0, max_func, depths(d+1, l)), depths(d+1, r));
                    append_assoc(depths(d+1, l), depths(d+1, r), s0);
                    build_rec_complete(n0, d+1, l, append(depths(d+1, r), s0));
                    
                    le_max(0, depths(d+1, l));
                    max_le_max(0, fold_left(0, max_func, depths(d+1, l)), depths(d+1, r));
                    build_rec_complete(n0, d+1, r, s0);
            }
    }
}

@*/

