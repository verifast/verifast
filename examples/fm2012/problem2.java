import java.util.Arrays;

/*@

fixpoint int power(int n, nat e) {
    switch (e) {
        case zero: return 1;
        case succ(e0): return n * pow(n, e0);
    }
}

inductive bintree = leaf(int) | node(bintree, bintree);

fixpoint bintree bintree_of_list(nat n, list<int> xs) {
    switch (n) {
        case zero: return leaf(head(xs));
        case succ(n0): return node(bintree_of_list(n0, take(length(xs) / 2, xs)), bintree_of_list(n0, drop(length(xs) / 2, xs)));
    }
}

lemma void pow_gt_zero(int m, nat n)
    requires 0 < m;
    ensures 0 < pow(m, n);
{
    assume(false);
}

lemma void flatten_bintree_of_list(nat n, list<int> xs)
    requires length(xs) == pow(2, n);
    ensures flatten(bintree_of_list(n, xs)) == xs;
{
    switch (n) {
        case zero:
            switch (xs) { case nil: case cons(x0, xs0): }
        case succ(n0):
            pow_gt_zero(2, n);
            append_take_drop(length(xs) / 2, xs);
            flatten_bintree_of_list(n0, take(length(xs) / 2, xs));
            //assume(length(xs) - length(xs) / 2 == length(xs) / 2);
            length_drop(length(xs) / 2, xs);
            assert length(drop(length(xs) / 2, xs)) == length(xs) / 2;
            flatten_bintree_of_list(n0, drop(length(xs) / 2, xs));
    }
}

fixpoint list<int> flatten(bintree t) {
    switch (t) {
        case leaf(n): return cons(n, nil);
        case node(t1, t2): return append(flatten(t1), flatten(t2));
    }
}

predicate array_tree0(int[] a, int left, int right, bintree values) =
    right > left + 1 ?
        array_tree0(a, left - (right - left) / 2, left, ?lvalues) &*&
        array_tree0(a, right - (right - left) / 2, right, ?rvalues) &*&
        values == node(lvalues, rvalues) &*&
        right - left == (right - left) / 2 * 2
    :
        array_element(a, left, ?l) &*& array_element(a, right, ?r) &*& values == node(leaf(l), leaf(r)) &*&
        right == left + 1;

lemma void array_slice_to_array_tree0(nat n)
    requires array_slice<int>(?a, ?start, ?end, ?vs) &*& length(vs) == pow(2, succ(n));
    ensures array_tree0(a, start + (end - start) / 2 - 1, end - 1, bintree_of_list(n, vs));
{
    switch (n) {
        case zero:
            switch (vs) { case nil: case cons(h, t): switch (t) { case nil: assert true; case cons(th, tt): assert tt == nil; assert true; } }
        case succ(n0):
            array_slice_to_array_tree0(n0);
            array_slice_to_array_tree0(n0);
    }
    close array_tree0(a, start + (end - start) / 2 - 1, end - 1, bintree_of_list(n, vs));
}

fixpoint int treesum(bintree t) {
    switch (t) {
        case leaf(n): return n;
        case node(n1, n2): return treesum(n1) + treesum(n2);
    }
}

fixpoint bintree getleft(bintree t) {
    switch (t) {
        case leaf(n): return t;
        case node(t1, t2): return t1;
    }
}

fixpoint bintree getright(bintree t) {
    switch (t) {
        case leaf(n): return t;
        case node(t1, t2): return t2;
    }
}

fixpoint boolean isleaf(bintree t) {
    switch (t) {
        case leaf(n): return true;
        case node(t1, t2): return false;
    }
}

predicate array_tree1(int[] a, int left, int right, bintree values) =
    right > left + 1 ?
        array_tree1(a, left - (right - left) / 2, left, ?lvalues) &*& array_element(a, left, treesum(lvalues)) &*&
        array_tree1(a, right - (right - left) / 2, right, ?rvalues) &*&
        values == node(lvalues, rvalues) &*&
        right - left == (right - left) / 2 * 2
    :
        array_element(a, left, ?l) &*& getleft(values) == leaf(l) &*& isleaf(getright(values)) == true &*& !isleaf(values) &*&
        right == left + 1;

predicate array_tree2(int[] a, int left, int right, int leftSum, bintree values) =
    right > left + 1 ?
        array_tree2(a, left - (right - left) / 2, left, leftSum, ?lvalues) &*&
        array_tree2(a, right - (right - left) / 2, right, leftSum + treesum(lvalues), ?rvalues) &*&
        values == node(lvalues, rvalues) &*&
        right - left == (right - left) / 2 * 2
    :
        array_element(a, left, leftSum) &*& array_element(a, right, ?r) &*& getleft(values) == leaf(r - leftSum) &*& !isleaf(values) &*& isleaf(getright(values)) == true &*&
        right == left + 1;

fixpoint list<int> prefixSums(int leftSum, bintree b) {
    switch (b) {
        case leaf(n): return cons(leftSum, nil);
        case node(t1, t2): return append(prefixSums(leftSum, t1), prefixSums(leftSum + treesum(t1), t2));
    }
}

lemma void array_tree2_prefixsums()
    requires array_tree2(?a, ?left, ?right, ?leftSum, ?values);
    ensures array_slice(a, left + 1 - (right - left), right + 1, prefixSums(leftSum, values));
{
    open array_tree2(_, _, _, _, _);
    if (right > left + 1) {
        array_tree2_prefixsums();
        array_tree2_prefixsums();
    } else {
        assert right == left + 1;
        switch (values) {
            case leaf(n): assert true;
            case node(t1, t2):
                switch (t2) {
                    case leaf (m): assert true;
                    case node(t21, t22): assert true;
                }
        }
    }
}

@*/

class PrefixSumRec {

    private int[] a;

    PrefixSumRec(int [] a)
        //@ requires true;
        //@ ensures this.a |-> a;
    {
	this.a = a;
    }


    public void upsweep(int left, int right)
        //@ requires a |-> ?a_ &*& array_tree0(a_, left, right, ?values);
        //@ ensures a |-> a_ &*& array_tree1(a_, left, right, values) &*& array_element(a_, right, treesum(values));
    {
        //@ open array_tree0(_, _, _, _);
        if (right > left+1) {
            int space = right - left;
            upsweep(left-space/2,left);
            upsweep(right-space/2,right);
        }
        a[right] = a[left]+a[right];
        //@ close array_tree1(a_, left, right, values);
    }
    

    public void downsweep(int left, int right)
        //@ requires a |-> ?a_ &*& array_tree1(a_, left, right, ?values) &*& array_element(a_, right, ?leftSum);
        //@ ensures a |-> a_ &*& array_tree2(a_, left, right, leftSum, values);
    {
        //@ open array_tree1(_, _, _, _);
        int tmp = a[right];
        a[right] = a[right] + a[left];
        a[left] = tmp;
        if (right > left+1) {
            int space = right - left;
            downsweep(left-space/2,left);
            downsweep(right-space/2,right);
        }
        //@ close array_tree2(a_, left, right, leftSum, values);
    }
    
    public static void prefixsums(int[] a)
        //@ requires array_slice(a, 0, a.length, ?vs) &*& exists<nat>(?n) &*& length(vs) == pow(2, n);
        //@ ensures array_slice(a, 0, a.length, prefixSums(0, bintree_of_list(n, vs)));
    {
        int left = a.length / 2 - 1;
        int right = a.length - 1;
        PrefixSumRec p = new PrefixSumRec(a);
        p.upsweep(left, right);
        a[a.length - 1]=0;
        p.downsweep(left, right);
        //@ array_tree2_prefixsums();
    }
    
    public static void main (String [] args)
        //@ requires true;
        //@ ensures true;
    {
        int [] a = {3,1,7,0,4,1,6,3};
        //@ close array_tree0(a, 0, 1, _);
        //@ close array_tree0(a, 2, 3, _);
        //@ close array_tree0(a, 1, 3, _);
        //@ close array_tree0(a, 4, 5, _);
        //@ close array_tree0(a, 6, 7, _);
        //@ close array_tree0(a, 5, 7, _);
        //@ close array_tree0(a, 3, 7, _);
        PrefixSumRec p = new PrefixSumRec(a);
        p.upsweep(3,7);
        a[7]=0;
        p.downsweep(3,7);
        //@ array_tree2_prefixsums();
        //@ assert array_slice(a, 0, a.length, cons(0, cons(3, cons(4, cons(11, cons(11, cons(15, cons(16, cons(22, nil)))))))));
    }

}


/*
[3, 1, 7, 0, 4, 1, 6, 3]
[3, 4, 7, 11, 4, 5, 6, 25]
[0, 3, 4, 11, 11, 15, 16, 22]



*/
