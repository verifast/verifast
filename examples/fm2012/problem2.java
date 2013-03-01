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

lemma void note(boolean b)
    requires b;
    ensures b;
{
}

lemma void pow2_gt_zero(nat n)
    requires true;
    ensures 0 < pow(2, n);
{
    switch (n) {
        case zero:
        case succ(n0):
            pow2_gt_zero(n0);
    }
}

lemma void flatten_bintree_of_list(nat n, list<int> xs)
    requires length(xs) == pow(2, n);
    ensures flatten(bintree_of_list(n, xs)) == xs;
{
    switch (n) {
        case zero:
            switch (xs) { case nil: case cons(x0, xs0): }
        case succ(n0):
            pow2_gt_zero(n);
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
    0 <= left &*& left < right &*&
    right > left + 1 ?
        array_tree0(a, left - (right - left) / 2, left, ?lvalues) &*&
        array_tree0(a, right - (right - left) / 2, right, ?rvalues) &*&
        values == node(lvalues, rvalues) &*&
        right - left == (right - left) / 2 * 2
    :
        array_element(a, left, ?l) &*& array_element(a, right, ?r) &*& values == node(leaf(l), leaf(r)) &*&
        right == left + 1;

lemma void even_lemma(int x)
    requires x == x / 2 * 2;
    ensures x - x / 2 == x / 2;
{
}

lemma void array_slice_to_array_tree0(nat n, int[] a, int start, int end)
    requires array_slice<int>(a, start, end, ?vs) &*& length(vs) == pow(2, succ(n));
    ensures array_tree0(a, start + (end - start) / 2 - 1, end - 1, bintree_of_list(succ(n), vs));
{
    switch (n) {
        case zero:
            switch (vs) { case nil: case cons(h, t): switch (t) { case nil: assert true; case cons(th, tt):
                assert tt == nil;
                assert take(length(vs) / 2, vs) == cons(h, nil);
                assert drop(length(vs) / 2, vs) == cons(th, nil);
                assert bintree_of_list(succ(zero), vs) == node(leaf(h), leaf(th));
                
            } }
            close array_tree0(a, start + (end - start) / 2 - 1, end - 1, bintree_of_list(succ(n), vs));
        case succ(n0):
            assert length(take(length(vs) / 2, vs)) == pow(2, n);
            array_slice_to_array_tree0(n0, a, start, start + (end - start) / 2);
            assert start + (end - start) / 2 - start == length(vs) / 2;
            assert length(vs) / 2 == pow(2, n);
            assert length(vs) >= (end - start) / 2;
            assert end - start == (end - start) / 2 * 2;
            note(end - start == (end - start) / 2 * 2);
            even_lemma(end - start);
            assert 0 <= (end - start) / 2;
            length_drop((end - start) / 2, vs);
            assert length(drop((end - start) / 2, vs)) == (end - start) - (end - start) / 2;
            assert length(drop((end - start) / 2, vs)) == pow(2, n);
            assert length(drop((end - start) / 2, drop(0, vs))) == pow(2, n);
            array_slice_to_array_tree0(n0, a, start + (end - start) / 2, end);
            pow2_gt_zero(n0);
            assert 0 < (end - start) / 2;
            assert end == start + (end - start) / 2 * 2;
            note(end == start + (end - start) / 2 * 2);
            assert end - start - (end - start) / 2 >= 2;
            assert end >= (start + (end - start) / 2) + 2;
            assert end - 1 > (start + (end - start) / 2 - 1) + 1;
            close array_tree0(a, start + (end - start) / 2 - 1, end - 1, bintree_of_list(succ(n), vs));
    }
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

fixpoint list<int> list_prefixSums(int leftSum, list<int> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x0, xs0): return cons(leftSum, list_prefixSums(leftSum + x0, xs0));
    }
}

fixpoint int sum(list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x0, xs0): return x0 + sum(xs0);
    }
}

lemma void sum_append(list<int> xs, list<int> ys)
    requires true;
    ensures sum(append(xs, ys)) == sum(xs) + sum(ys);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            sum_append(xs0, ys);
    }
}

lemma void sum_flatten(bintree b)
    requires true;
    ensures sum(flatten(b)) == treesum(b);
{
    switch (b) {
        case leaf(n):
        case node(b1, b2):
            sum_flatten(b1);
            sum_flatten(b2);
            sum_append(flatten(b1), flatten(b2));
    }
}

lemma void list_prefixSums_append(int leftSum, list<int> xs, list<int> ys)
    requires true;
    ensures list_prefixSums(leftSum, append(xs, ys)) == append(list_prefixSums(leftSum, xs), list_prefixSums(leftSum + sum(xs), ys));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            list_prefixSums_append(leftSum + x0, xs0, ys);
    }
}

lemma void list_prefixSums_flatten(int leftSum, bintree b)
    requires true;
    ensures prefixSums(leftSum, b) == list_prefixSums(leftSum, flatten(b));
{
    switch (b) {
        case leaf(n):
        case node(b1, b2):
            list_prefixSums_flatten(leftSum, b1);
            list_prefixSums_flatten(leftSum + treesum(b1), b2);
            sum_flatten(b1);
            list_prefixSums_append(leftSum, flatten(b1), flatten(b2));
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
        //@ requires array_slice(a, 0, a.length, ?vs) &*& exists<nat>(?n) &*& length(vs) == pow(2, succ(n));
        //@ ensures array_slice(a, 0, a.length, list_prefixSums(0, vs));
    {
        int left = a.length / 2 - 1;
        int right = a.length - 1;
        PrefixSumRec p = new PrefixSumRec(a);
        //@ array_slice_to_array_tree0(n, a, 0, a.length);
        p.upsweep(left, right);
        a[a.length - 1]=0;
        p.downsweep(left, right);
        //@ array_tree2_prefixsums();
        //@ flatten_bintree_of_list(succ(n), vs);
        //@ list_prefixSums_flatten(0, bintree_of_list(succ(n), vs));
    }
    
    public static void main (String [] args)
        //@ requires true;
        //@ ensures true;
    {
        int [] a = {3,1,7,0,4,1,6,3};
        //@ close exists(succ(succ(zero)));
        prefixsums(a);
        //@ assert a[..] |-> {0,3,4,11,11,15,16,22};
    }

}
