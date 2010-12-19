/*@
fixpoint boolean consistent(list<int> vs, nat i, int pos) {
  switch(i) {
    case zero: return true;
    case succ(j): return nth(int_of_nat(j), vs) != nth(pos, vs) &&
                  pos - int_of_nat(j) != ((int)nth(pos, vs)) - ((int) nth(int_of_nat(j), vs)) &&
                  int_of_nat(j) - pos  != ((int) nth(int_of_nat(j), vs)) - nth(pos, vs) &&
                  consistent(vs, j, pos);
  }
}

fixpoint boolean allconsistent(list<int> vs, nat n) {
  switch(n) {
    case zero: return true;
    case succ(n0): return consistent(vs, n0, int_of_nat(n0)) && allconsistent(vs, n0);
  }
}

lemma void take_consistent(list<int> vs, nat i, int pos) 
  requires consistent(vs, i, pos) == true &*& 0 <= int_of_nat(i) &*& int_of_nat(i) <= pos &*& pos < length(vs);
  ensures consistent(take(pos + 1, vs), i, pos) == true;
{
  switch(i) {
    case zero:
    case succ(i0):
       nth_take(int_of_nat(i0), pos + 1, vs);
       nth_take(pos, pos + 1, vs);
       take_consistent(vs, i0, pos); 
  }
}

lemma void nth_append<t>(list<t> vs1, list<t> vs2, int n) 
  requires 0<=n &*& n < length(append(vs1, vs2));
  ensures nth(n, append(vs1, vs2)) == (n < length(vs1) ? nth(n, vs1) : nth(n - length(vs1), vs2));
{ 
  switch(vs1) {
    case nil:
    case cons(h, t):
      if(n == 0) {
      } else {
        nth_append<t>(t, vs2, n - 1);
      }
  }  
}
  

lemma void append_consistent(list<int> vs, nat n, int pos, list<int> vs2)
  requires consistent(vs, n, pos) == true && int_of_nat(n) < length(vs) && 0<= pos &*& pos < length(vs);
  ensures consistent(append(vs, vs2), n, pos) == true;
{
  switch(n) {
    case zero:
    case succ(n0): 
      nth_append(vs, vs2, int_of_nat(n0));
      nth_append(vs, vs2, pos);
      append_consistent(vs, n0, pos, vs2);
  }
}
  

lemma void append_allconsistent(list<int> vs, nat n, list<int> vs2)
  requires allconsistent(vs, n) == true &*& int_of_nat(n) <= length(vs);
  ensures allconsistent(append(vs, vs2), n) == true;
{
  switch(n) {
    case zero:
    case succ(n0):
      append_consistent(vs, n0, int_of_nat(n0), vs2);
      append_allconsistent(vs, n0, vs2);
  }
}

lemma void take_one_extra<t>(list<t> vs, int n) 
  requires 0<=n &*& n < length(vs);
  ensures take(n + 1, vs) == append(take(n, vs), cons(nth(n, vs), nil));
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(n == 0) {
      } else  {
        take_one_extra(t, n - 1);
      }
  }
}

lemma void take_allconsistent(list<int> vs, nat n) 
  requires allconsistent(vs, n) == true &*& int_of_nat(n) <= length(vs);
  ensures allconsistent(take(int_of_nat(n), vs), n) == true;
{
  switch(n) {
    case zero:
    case succ(n0):
      take_consistent(vs, n0, int_of_nat(n0));
      take_allconsistent(vs, n0);
      succ_int(int_of_nat(n0));
      append_allconsistent(take(int_of_nat(n0), vs), n0, cons(nth(int_of_nat(n0), vs), nil));
      take_one_extra(vs, int_of_nat(n0)); 
  }
}

lemma void take_append<t>(list<t> vs1, list<t> vs2, int n)
  requires 0 <= n && n <= length(append(vs1, vs2)) && n <= length(vs1);
  ensures take(n, append(vs1, vs2)) == (n <= length(vs1) ? take(n, vs1) : append(vs1, take(n - length(vs1), vs2)));
{
  switch(vs1) {
    case nil:
    case cons(h, t): 
      if(n == 0) {
      } else {
        take_append(t, vs2, n- 1);
      }
  }
}

lemma void not_consistent_successor(list<int> vs, nat n, int pos) 
  requires !consistent(vs, n, pos) &*& int_of_nat(n) < pos;
  ensures ! consistent(vs, succ(n), pos);
{
}



lemma void not_consistent_monotonic(list<int> vs, int pos, nat m)
  requires ! consistent(vs, nat_of_int(pos - int_of_nat(m)), pos) &*& 0 <= int_of_nat(m) &*& int_of_nat(m) <= pos;
  ensures ! consistent(vs, nat_of_int(pos), pos);
{
  switch(m) {
    case zero:
    case succ(m0):
      minuslemma(int_of_nat(m), pos);
      not_consistent_monotonic(vs, pos, m0);
  }
}

lemma void take_oke(list<int> vs1, list<int> vs2, int i)
  requires 0 <= i &*& i < length(vs1) &*& length(vs2) == length(vs1) &*& take(i + 1, vs1) == take(i + 1, vs2);
  ensures take(i, vs1) == take(i, vs2);
{
  switch(vs1) {
    case nil:
    case cons(h1, t1):
      switch(vs2) {
        case nil:
        case cons(h2, t2):
          if(h1 != h2) {
          } else {
            if(i == 0) {
            } else {
              take_oke(t1, t2, i - 1);
            }
          }
      }
    
  }
}

@*/

class NQueens {
  static boolean isConsistent(int[] board, int pos) 
    //@ requires board != null &*& array_slice(board, 0, board.length, ?vs) &*& 0 <= pos && pos < board.length;
    //@ ensures array_slice(board, 0, board.length, vs) &*& result == consistent(vs, nat_of_int(pos), pos);
  {
    int bp = board[pos];
    for(int i = 0; i < pos; i++) 
      //@ invariant 0 <= i &*& i <= pos &*& array_slice(board, 0, board.length, vs) &*& consistent(vs, nat_of_int(i), pos) == true;
    {
      int bi = board[i];
      //@ succ_int(i);
      if(bi == bp || pos - i == bp - bi || i - pos == bi - bp) {
        //@ not_consistent_monotonic(vs, pos, nat_of_int(pos - i - 1));
        return false;
      }
    }
    return true;
  }
  
  static int[] search(int[] board, int pos)
    //@ requires board != null &*& array_slice(board, 0, board.length, ?vs) &*& 0 <= pos && pos <= board.length &*& allconsistent(vs, nat_of_int(pos)) == true;
    /*@ ensures array_slice(board, 0, board.length, ?vs2) &*& result == null  ? 
                  take(pos, vs) == take(pos, vs2) &*&
                  allconsistent(vs2, nat_of_int(pos)) == true 
                  /* todo: specify here that append(take(pos, vs), all lists of board.length - pos) are not allconsistent */
                  : 
                  result == board &*& allconsistent(vs2, nat_of_int(length(vs2))) == true; @*/
  {
    if(pos == board.length) {
      return board;
    } else {
      for(int i = 0; i < board.length; i++) 
        //@ invariant array_slice(board, 0, board.length, ?vs2) &*& take(pos, vs) == take(pos, vs2) &*& allconsistent(vs2, nat_of_int(pos)) == true;
      {
        board[pos] = i;
        //@ assert array_slice(board, 0, board.length, ?vs3);
        //@ take_append(take(pos, vs2), append(cons(i, nil), take(length(vs2) - pos - 1, tail(drop(pos, vs2)))), pos);
        //@ take_allconsistent(vs2, nat_of_int(pos));
        //@ append_allconsistent(take(pos, vs2), nat_of_int(pos), append(cons(i, nil), take(length(vs2) - pos - 1, tail(drop(pos, vs2)))));
        if(isConsistent(board, pos)) {
          //@ succ_int(pos);
          int[] s = search(board, pos + 1);
          if(s != null) {
            return s;
          }
          //@ assert array_slice(board, 0, board.length, ?vs4);
          //@ take_oke(vs3, vs4, pos);
        }
      }
      return null;
    }
  }
  
  static int[] startsearch(int[] board) 
    //@ requires board != null &*& array_slice(board, 0, board.length, ?vs);
    //@ ensures array_slice(board, 0, board.length, ?vs2);
  {
    return search(board, 0);
  }
}