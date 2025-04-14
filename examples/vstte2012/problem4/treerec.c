//@ #include "nat.gh"
//@ #include "listex.gh"

#include "treerec_list.h"
#include "treerec_tree.h"

/*@

fixpoint list<int> depths(int d, tree t) {
    switch (t) {
        case leaf: return cons(d, nil);
        case node(l, r): return append(depths(d+1, l), depths(d+1, r));
    }
}

inductive result = success(tree, list<int>) | fail;

fixpoint result build_rec0(nat n, int d, list<int> s) {
    switch (n) {
        case zero: return fail;
        case succ(n0): return
            switch (s) {
                 case nil: return fail;
                 case cons(h, s1): return
                     h < d ? fail :
                     h == d ? success(leaf, s1) :
                     switch (build_rec0(n0, d+1, s)) {
                         case fail: return fail;
                         case success(l, s2): return
                             switch (build_rec0(n0, d+1, s2)) {
                                 case fail: return fail;
                                 case success(r, s3): return
                                     success(node(l, r), s3);
                             };
                     };
            };
   }
}

lemma void test_suite()
    requires true;
    ensures true;
{
    nat n0 = zero;
    nat n1 = succ(n0);
    nat n2 = succ(n1);
    nat n3 = succ(n2);
    nat n4 = succ(n3);
    
    assert build_rec0(n4, 0, cons(1, cons(3, cons(3, cons(2, nil))))) == success(node(leaf, node(node(leaf, leaf), leaf)), nil);
    assert build_rec0(n4, 0, cons(1, cons(3, cons(2, cons(2, nil))))) == fail;
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
        switch (build_rec0(n, d, s)) {
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
                         switch (build_rec0(n0, d+1, s)) {
                             case fail:
                             case success(l, s2):
                                 build_rec_sound(n0, d+1, s2);
                                 switch (build_rec0(n0, d+1, s2)) {
                                     case fail:
                                     case success(r, s3):
                                         append_assoc(depths(d+1, l), depths(d+1, r), s3);
                                 }
                         }
                     }
             }
    }
}

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
    ensures build_rec0(n, d, append(depths(d, t), s0)) == success(t, s0);
{
    switch (n) {
        case zero:
            depths_head(d, t);
            le_max(max_func(d, head(depths(d, t))), tail(depths(d, t)));
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

// <begin> Some overhead for hiding the annoying 'nat n' argument. Would not be needed if VeriFast supported recursion on int.

fixpoint result build_rec1(int d, list<int> ds) {
    return build_rec0(succ(nat_of_int(fold_left(0, max_func, ds) - d)), d, ds);
}

lemma void build_rec0_n_le(nat n0, nat n1, int d, list<int> ds)
    requires fold_left(0, max_func, ds) - d < int_of_nat(n0) &*& int_of_nat(n0) <= int_of_nat(n1);
    ensures build_rec0(n0, d, ds) == build_rec0(n1, d, ds);
{
    switch (n1) {
        case zero:
            switch (n0) { case zero: case succ(n00): }
        case succ(n10):
            switch (n0) {
                case zero:
                    switch (ds) {
                        case nil:
                        case cons(h, ds0):
                            le_max(max_func(0, h), ds0);
                    }
                case succ(n00):
                    switch (ds) {
                        case nil:
                        case cons(h, ds0):
                            if (h < d) {
                            } else if (h == d) {
                            } else {
                                build_rec0_n_le(n00, n10, d+1, ds);
                                switch (build_rec0(n00, d+1, ds)) {
                                    case fail:
                                    case success(l0, ds10):
                                        switch (build_rec0(n10, d+1, ds)) {
                                            case fail:
                                            case success(l1, ds11):
                                                build_rec_sound(n00, d+1, ds);
                                                fold_left_append(0, max_func, depths(d+1, l0), ds10);
                                                le_max(0, depths(d+1, l0));
                                                max_le_max(0, fold_left(0, max_func, depths(d+1, l0)), ds10);
                                                build_rec0_n_le(n00, n10, d+1, ds10);
                                                switch (build_rec0(n00, d+1, ds10)) {
                                                    case fail:
                                                    case success(r0, ds20):
                                                        switch (build_rec0(n10, d+1, ds11)) {
                                                            case fail:
                                                            case success(r1, ds21):
                                                        }
                                                }
                                        }
                                }
                            }
                    }
            }
    }
}

lemma void note(bool b)
    requires b;
    ensures b;
{
}

lemma void build_rec1_eq(int d, list<int> s)
    requires true;
    ensures
        build_rec1(d, s) ==
	    switch (s) {
		 case nil: return fail;
		 case cons(h, s1): return
		     h < d ? fail :
		     h == d ? success(leaf, s1) :
		     switch (build_rec1(d+1, s)) {
		         case fail: return fail;
		         case success(l, s2): return
		             switch (build_rec1(d+1, s2)) {
		                 case fail: return fail;
		                 case success(r, s3): return
		                     success(node(l, r), s3);
		             };
		     };
	    };
{
    switch (s) {
        case nil:
        case cons(h, s1):
            if (h < d) {
            } else if (h == d) {
            } else {
                le_max(max_func(0, h), s1);
                note(fold_left(0, max_func, s) >= h);
                assert h > d;
                assert fold_left(0, max_func, s) > d;
                build_rec0_n_le(succ(nat_of_int(fold_left(0, max_func, s) - d - 1)), nat_of_int(fold_left(0, max_func, s) - d), d+1, s);
                switch (build_rec1(d+1, s)) {
                    case fail:
                    case success(l, s2):
                        build_rec_sound(succ(nat_of_int(fold_left(0, max_func, s) - d - 1)), d+1, s);
                        fold_left_append(0, max_func, depths(d+1, l), s2);
                        le_max(0, depths(d+1, l));
                        max_le_max(0, fold_left(0, max_func, depths(d+1, l)), s2);
                        assert fold_left(0, max_func, s2) - d <= fold_left(0, max_func, s) - d;
                        if (fold_left(0, max_func, s2) - d - 1 < 0) {
                            switch (s2) {
                                case nil:
                                    assert build_rec1(d+1, s2) == fail;
                                    assert build_rec0(nat_of_int(fold_left(0, max_func, s) - d), d+1, s2) == fail;
                                    assert true;
                                case cons(s2h, s2t):
                                    le_max(max_func(0, s2h), s2t);
                                    assert s2h <= d;
                                    assert build_rec1(d+1, s2) == fail;
                                    assert build_rec0(nat_of_int(fold_left(0, max_func, s) - d), d+1, s2) == fail;
                                    assert true;
                            }
                        } else {
                            build_rec0_n_le(succ(nat_of_int(fold_left(0, max_func, s2) - d - 1)), nat_of_int(fold_left(0, max_func, s) - d), d+1, s2);
                        }
                        switch (build_rec1(d+1, s2)) {
                            case fail:
                                assert true;
                            case success(r, s3):
                                assert true;
                        }
                }
            }
    }
}

// <end> Some overhead for hiding the annoying 'nat n' argument. Would not be needed if VeriFast supported recursion on int.

@*/

bool build_rec(int d, struct list *s, struct tree **t)
    //@ requires list(s, ?vs) &*& *t |-> _;
    /*@
    ensures list(s, ?rvs) &*&
        switch (build_rec1(d, vs)) {
            case fail: return *t |-> _ &*& result == false;
            case success(rvt, rvs0): return *t |-> ?rt &*& result == true &*& rvs == rvs0 &*& tree(rt, rvt);
        };
    @*/
    // decreases max_func(0, fold_left(0, max_func, vs) - d); // Not yet checked by VeriFast.
{
    //@ build_rec1_eq(d, vs);
    struct tree *l;
    struct tree *r;
    if (list_is_empty(s)) return false;
    int h = list_head(s);
    if (h < d) return false;
    if (h == d) { list_pop(s); struct tree *leaf = create_leaf(); *t = leaf; return true; }
    if (!build_rec(d+1, s, &l)) return false;
    if (!build_rec(d+1, s, &r)) { tree_dispose(l); return false; }
    struct tree *node = create_node(l, r); *t = node;
    return true;
}

/*@

// The bottom line

inductive build_result = build_success(tree t) | build_fail;

fixpoint build_result build0(list<int> s) {
    return switch (build_rec1(0, s)) {
        case fail: return build_fail;
        case success(rt, rs): return
            rs == nil ? build_success(rt) : build_fail;
    };
}

lemma void build_sound(list<int> s)
    requires true;
    ensures switch (build0(s)) { case build_fail: return true; case build_success(t): return s == depths(0, t); };
{
    build_rec_sound(succ(nat_of_int(fold_left(0, max_func, s))), 0, s);
}

lemma void build_complete(tree t)
    requires true;
    ensures build0(depths(0, t)) == build_success(t);
{
    build_rec_complete(succ(nat_of_int(fold_left(0, max_func, depths(0, t)))), 0, t, nil);
}

@*/

bool build(struct list *s, struct tree **t)
    //@ requires list(s, ?vs) &*& *t |-> _;
    /*@
    ensures list(s, ?rvs) &*&
    switch (build0(vs)) {
        case build_fail: return *t |-> _ &*& result == false;
        case build_success(rvt): return *t |-> ?rt &*& result == true &*& tree(rt, rvt) &*& rvs == nil;
    };
    @*/
{
    if (!build_rec(0, s, t)) return false;
    if (!list_is_empty(s)) {
        tree_dispose(*t);
        return false;
    }
    return true;
}

// Below follows some infrastructure for checking trees, and the test suite in C code.

/*@

inductive check_result = check_fail | check_success(list<char> rest);

fixpoint check_result check_tree_pure(tree t, list<char> spec) {
    switch (t) {
        case leaf: return head(spec) == 'L' ? check_success(tail(spec)) : check_fail;
        case node(l, r): return head(spec) != 'N' ? check_fail :
            switch (check_tree_pure(l, tail(spec))) {
                case check_fail: return check_fail;
                case check_success(spec1): return check_tree_pure(r, spec1);
            };
    }
}

@*/

char *check_tree(struct tree *t, char *spec)
    //@ requires tree(t, ?v) &*& [_]string(spec, ?cs);
    /*@
    ensures
        switch (check_tree_pure(v, cs)) {
            case check_fail: return result == 0;
            case check_success(cs0): return result != 0 &*& [_]string(result, cs0);
        };
    @*/
{
    bool b = tree_is_leaf(t);
    //@ string_limits(spec);
    //@ open string(spec, _);
    if (*spec == 'L') {
        tree_dispose(t);
        if (!b) return 0;
        return spec + 1;
    } else if (*spec == 'N') {
        struct tree *l;
        struct tree *r;
        if (b) { tree_dispose(t); return 0; }
        tree_destruct_node(t, &l, &r);
        spec = check_tree(l, spec + 1);
        if (spec == 0) { tree_dispose(r); return 0; }
        return check_tree(r, spec);
    } else {
        tree_dispose(t);
        return 0;
    }
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct tree *t;
    bool b;
    
    struct list *l = create_list();
    list_push(l, 2);
    list_push(l, 3);
    list_push(l, 3);
    list_push(l, 1);
    //@ note(nat_of_int(3) == succ(succ(succ(zero))));
    b = build(l, &t);
    assert(b);
    char *result = check_tree(t, "NLNNLLL");
    assert(result != 0);
    list_dispose(l);
    
    l = create_list();
    list_push(l, 2);
    list_push(l, 2);
    list_push(l, 3);
    list_push(l, 1);
    b = build(l, &t);
    assert(!b);
    list_dispose(l);
    
    return 0;
}