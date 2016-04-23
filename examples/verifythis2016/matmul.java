/*@

predicate vector(int[] X, int m; list<int> values) = X[..] |-> values &*& X.length == m;

predicate vectors(int[][] XsArray, list<int[]> Xs, int m; list<list<int> > vss) =
    switch (Xs) {
        case nil: return vss == nil;
        case cons(X, Xs0): return vector(X, m, ?vs) &*& vectors(XsArray, Xs0, m, ?vss0) &*& vss == cons(vs, vss0);
    };

predicate matrix(int[][] X, int n, int m; list<list<int> > rows) =
    X[..] |-> ?rowArrays &*& n == X.length &*&
    vectors(X, rowArrays, m, rows);

fixpoint int matrix_elem(list<list<int> > rows, int i, int j) { return nth(j, nth(i, rows)); }

fixpoint nat len<t>(list<t> xs) {
    switch (xs) {
        case nil: return zero;
        case cons(x, xs0): return succ(len(xs0));
    }
}

lemma_auto void len_eq_nat_of_int_length<t>(list<t> xs)
    requires true;
    ensures len(xs) == nat_of_int(length(xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            len_eq_nat_of_int_length(xs0);
    }
}

fixpoint int matrix_multiply_elem(list<int> Arow, int j, list<list<int> > Brows) {
    switch (Arow) {
        case nil: return 0;
        case cons(vA, Arow0): return vA * nth(j, head(Brows)) + matrix_multiply_elem(Arow0, j, tail(Brows));
    }
}

fixpoint list<int> matrix_multiply_row(nat fuel, list<int> row, int j, list<list<int> > B) {
    switch (fuel) {
        case zero: return nil;
        case succ(fuel0): return cons(matrix_multiply_elem(row, j, B), matrix_multiply_row(fuel0, row, j + 1, B));
    }
}

fixpoint list<list<int> > matrix_multiply(list<list<int> > A, list<list<int> > B) {
    switch (A) {
        case nil: return nil;
        case cons(row, rows0): return cons(matrix_multiply_row(len(row), row, 0, B), matrix_multiply(rows0, B));
    }
}

@*/

class Math {

    static void matrixMultiply(int[][] A, int[][] B, int[][] C)
    //@ requires [_]matrix(A, ?N, N, ?Arows) &*& [_]matrix(B, N, N, ?Brows) &*& matrix(C, N, N, _);
    //@ ensures matrix(C, N, N, matrix_multiply(Arows, Brows));
    {
        //@ open matrix(A, _, _, _);
        //@ open matrix(C, _, _, _);
        int n = A.length;
        //@ assert C[..] |-> ?CrowArrays;
        //@ assert [_]A[..] |-> ?ArowArrays;
        
        for (int i = 0; ; )
            /*@
            requires
                C[i..] |-> drop(i, CrowArrays) &*& vectors(C, drop(i, CrowArrays), N, _) &*& [_]matrix(B, N, N, Brows) &*&
                [_]A[i..] |-> drop(i, ArowArrays) &*& [_]vectors(A, drop(i, ArowArrays), N, ?Arows1) &*& length(CrowArrays) == length(ArowArrays);
            @*/
            //@ ensures C[old_i..] |-> drop(old_i, CrowArrays) &*& vectors(C, drop(old_i, CrowArrays), N, matrix_multiply(Arows1, Brows));
        {
            if (i >= n) {
                //@ open vectors(C, nil, N, _);
                //@ open vectors(A, nil, N, _);
                break;
            }
            //@ drop_n_plus_one(i, CrowArrays);
            //@ drop_n_plus_one(i, ArowArrays);
            int[] ArowArray = A[i];
            int[] CrowArray = C[i];
            //@ open [_]vectors(A, drop(i, ArowArrays), _, _);
            //@ assert [_]vectors(A, drop(i + 1, ArowArrays), N, tail(Arows1));
            //@ assert [_]ArowArray[..] |-> ?Arow;
            //@ open vectors(C, drop(i, CrowArrays), _, _);
            //@ assert CrowArray[..] |-> ?Crow;
            //@ assert len(Arow) == len(Crow);
            for (int j = 0; ; )
                //@ requires [_]ArowArray[..] |-> Arow &*& [_]matrix(B, N, N, Brows) &*& CrowArray[j..] |-> ?xs &*& 0 <= j;
                //@ ensures CrowArray[old_j..] |-> matrix_multiply_row(len(xs), Arow, old_j, Brows);
            {
                //@ switch (xs) { case nil: case cons(h, t): }
                if (j >= n) {
                    break;
                }
                CrowArray[j] = 0;
                //@ open [_]matrix(B, _, _, _);
                //@ assert [_]B[..] |-> ?BrowArrays;
                for (int k = 0; k < n; k++)
                    //@ requires CrowArray[j] |-> ?x &*& [_]ArowArray[k..] |-> drop(k, Arow) &*& [_]B[k..] |-> drop(k, BrowArrays) &*& [_]vectors(B, drop(k, BrowArrays), N, ?Brows1) &*& 0 <= k;
                    //@ ensures CrowArray[j] |-> x + matrix_multiply_elem(drop(old_k, Arow), j, Brows1);
                {
                    //@ drop_n_plus_one(k, Arow);
                    //@ drop_n_plus_one(k, BrowArrays);
                    //@ open [_]vectors(B, drop(k, BrowArrays), _, _);
                    int[] BrowArray = B[k];
                    //@ open [_]vector(BrowArray, _, _);
                    //@ assert [_]BrowArray[..] |-> ?Brow &*& BrowArray.length == N;
                    CrowArray[j] += ArowArray[k] * BrowArray[j];
                }
                //@ assert CrowArray[j] |-> matrix_multiply_elem(Arow, j, Brows);
                j++;
                //@ recursive_call();
                
            }
            i++;
            //@ recursive_call();
            
            //@ assert [_]vectors(A, drop(old_i + 1, ArowArrays), N, tail(Arows1));
            //@ assert vectors(C, drop(old_i + 1, CrowArrays), N, matrix_multiply(tail(Arows1), Brows));
            //@ assert CrowArray[..] |-> matrix_multiply_row(len(head(Arows1)), head(Arows1), 0, Brows);
            //@ close vectors(C, drop(old_i, CrowArrays), N, matrix_multiply(Arows1, Brows));
            
        }
        //@ close matrix(C, N, N, _);
    }
}