/*@

lemma_auto void length_append_auto<t>(list<t> xs, list<t> ys)
    requires true;
    ensures length(append(xs, ys)) == length(xs) + length(ys);
{
    length_append(xs, ys);
}

fixpoint boolean consistent(list<int> vs, nat i, int pos) {
  switch(i) {
    case zero: return true;
    case succ(j): return nth(int_of_nat(j), vs) != nth(pos, vs) &&
                  pos - int_of_nat(j) != ((int)nth(pos, vs)) - ((int) nth(int_of_nat(j), vs)) &&
                  pos - int_of_nat(j) != ((int) nth(int_of_nat(j), vs)) - nth(pos, vs) &&
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
  requires  0 <= int_of_nat(i) &*& int_of_nat(i) <= pos &*& pos < length(vs);
  ensures consistent(vs, i, pos) == consistent(take(pos + 1, vs), i, pos);
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
  requires int_of_nat(n) < length(vs) && 0<= pos &*& pos < length(vs);
  ensures consistent(vs, n, pos) == consistent(append(vs, vs2), n, pos);
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
  requires 0 <= n &*& n <= length(append(vs1, vs2)) &*& n <= length(vs1);
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

fixpoint list<t> update2<t>(unit u, list<t> vs, t v, int pos) {
  switch(u) {
    case unit: return append(take(pos, vs), append(cons(v, nil), tail(drop(pos, vs))));
  }
}

lemma_auto(update(pos, v, vs)) void update_eq_update2<t>(list<t> vs, t v, int pos)
  requires 0 <= pos && pos < length(vs);
  ensures update(pos, v, vs) == update2(unit, vs, v, pos);
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(pos == 0) {
      } else {
        update_eq_update2(t, v, pos - 1);
      }
  }
}

lemma void update_nth<t>(list<t> vs, t v, int pos) 
  requires nth(pos, vs) == v && 0 <= pos && pos < length(vs);
  ensures update2(unit, vs, v, pos) == vs;
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(pos == 0 ){
      } else {
        update_nth(t, v, pos - 1);
      }
  }
}

lemma void update_append<t>(list<t> vs, t v, int pos, list<t> vs2) 
  requires 0 <= pos &*& pos < length(vs);
  ensures append(update2(unit, vs, v, pos), vs2) == update2(unit, append(vs, vs2), v, pos);
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(pos == 0 ){
      } else {
        update_append<t>(t, v, pos - 1, vs2);
      }
  }
}

predicate inconsistent(list<int> vs, nat i, int pos) =
  (switch(i) { 
    case zero: return true; 
    case succ(i0): 
    return pos < length(vs) &*& inconsistent(vs, i0, pos) &*& 
    (consistent(update2(unit, vs, int_of_nat(i0), pos), nat_of_int(pos), pos) == true ? 
      inconsistent(update2(unit, vs, int_of_nat(i0), pos), nat_of_int(length(vs)), pos + 1) : true); }) ;

lemma void duplicate_inconsistent(list<int> vs, nat i, int pos) 
  requires inconsistent(vs, i, pos);
  ensures inconsistent(vs, i, pos) &*& inconsistent(vs, i, pos);
{
  open inconsistent(vs, i, pos);
  switch(i) {
    case zero: close inconsistent(vs, zero, pos); close inconsistent(vs, zero, pos);
    case succ(i0):
      duplicate_inconsistent(vs,  i0, pos);      
      if(consistent(update2(unit, vs, int_of_nat(i0), pos), nat_of_int(pos), pos)) {
        duplicate_inconsistent(update2(unit, vs, int_of_nat(i0), pos), nat_of_int(length(vs)), pos + 1);
        close inconsistent(vs, i, pos);
        close inconsistent(vs, i, pos);
      } else {
        close inconsistent(vs, i, pos);
        close inconsistent(vs, i, pos);
      }
  }
}

lemma_auto(take(j, update(i, v, vs))) void take_update2<t>(list<t> vs, t v, int i, int j)
  requires 0 <= i && i < length(vs) && 0 <= j && j <= i;
  ensures take(j, vs) == take(j, update(i, v, vs));
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(j == 0) {
      } else {
        take_update2(t, v, i - 1, j - 1);
      }
  }
}

lemma void length_update2<t>(list<t> vs, t v, int pos)
  requires 0 <= pos && pos < length(vs);
  ensures length(update2(unit, vs, v, pos)) == length(vs);
{
  switch(vs) {
    case nil: 
    case cons(h, t):
      if(pos == 0) {
      } else {
        length_update2(t, v, pos - 1);
      }
  } 
}

lemma void update_same(list<int> vs, list<int> vs2, int pos, int v)
  requires length(vs) == length(vs2) && take(pos, vs) == take(pos, vs2) &*& 0 <= pos &*& pos < length(vs);
  ensures take(pos + 1, update2(unit, vs, v, pos)) == take(pos + 1, update2(unit, vs2, v, pos));
{
  take_append(take(pos, vs), append(cons(v, nil), tail(drop(pos, vs))), pos);
  take_append(take(pos, vs2), append(cons(v, nil), tail(drop(pos, vs2))), pos);
  nth_append(take(pos, vs2), append(cons(v, nil), tail(drop(pos, vs2))), pos);
  nth_append(take(pos, vs), append(cons(v, nil), tail(drop(pos, vs))), pos);
  take_one_extra(update2(unit, vs, v, pos), pos);
  take_one_extra(update2(unit, vs2, v, pos), pos);
}

lemma void inconsistent_preserved(list<int> vs, int pos, list<int> vs2)
  requires ! consistent(vs, nat_of_int(pos), pos) &*& length(vs2) == length(vs) && take(pos + 1, vs) == take(pos + 1, vs2) &*& 0 <= pos &*& pos < length(vs);
  ensures ! consistent(vs2, nat_of_int(pos), pos);
{
  take_consistent(vs, nat_of_int(pos), pos);
  take_consistent(vs2, nat_of_int(pos), pos);
}

lemma void inconsistent_take_core(list<int> vs, nat i, int pos, list<int> vs2)
  requires inconsistent(vs, i, pos) &*& length(vs) == length(vs2) &*& take(pos, vs) == take(pos, vs2) &*& 0 <= pos;
  ensures inconsistent(vs2, i, pos);
{
  open inconsistent(vs, i, pos);
  switch(i) {
    case zero: close inconsistent(vs2, i, pos);
    case succ(i0):
      inconsistent_take_core(vs, i0, pos, vs2);
      length_update2(vs, int_of_nat(i0), pos);
      length_update2(vs2, int_of_nat(i0), pos);
      update_same(vs, vs2, pos, int_of_nat(i0));
      if(consistent(update2(unit, vs, int_of_nat(i0), pos), nat_of_int(pos), pos)) {
        inconsistent_take_core(update2(unit, vs, int_of_nat(i0), pos), nat_of_int(length(vs)), pos + 1, update2(unit, vs2, int_of_nat(i0), pos));
        close inconsistent(vs2, i, pos);
      } else {
        inconsistent_preserved(update2(unit, vs, int_of_nat(i0), pos), pos, update2(unit, vs2, int_of_nat(i0), pos));
        close inconsistent(vs2, i, pos);
      }
  }
}


  

lemma void inconsistent_take(list<int> vs, nat i, int pos, list<int> vs2)
  requires length(vs) == length(vs2) &*& take(pos, vs) == take(pos, vs2) &*& inconsistent(vs, i, pos) &*& 0 <= pos;
  ensures inconsistent(vs, i, pos) &*& inconsistent(vs2, i, pos);
{
  duplicate_inconsistent(vs,  i, pos);
  inconsistent_take_core(vs, i, pos, vs2);
}

fixpoint boolean inrange(list<int> vs, int max) {
  switch(vs) {
    case nil: return true;
    case cons(h, t): return 0 <= h && h < max && inrange(t, max);
  }
}

lemma void inrange_update_array(list<int> vs, int max, int v, int pos)
  requires 0 <= pos && pos < length(vs) && 0 <= v && v < max && inrange(vs, max);
  ensures inrange(update(pos, v, vs), max) == true; 
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(pos == 0) {
      } else {
        inrange_update_array(t, max, v, pos - 1);
      }
  }
}

lemma void inrange_update(list<int> vs, int max, int v, int pos)
  requires 0 <= pos && pos < length(vs) && 0 <= v && v < max && inrange(vs, max);
  ensures inrange(update2(unit, vs, v, pos), max) == true; 
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(pos == 0) {
      } else {
        inrange_update(t, max, v, pos - 1);
      }
  }
}

lemma void inrange_all_eq(list<int> vs, int max, int i)
  requires 0 < max && 0 <= i && i < max && all_eq(vs, i);
  ensures inrange(vs, max) == true; 
{
  switch(vs) {
    case nil:
    case cons(h, t):
      inrange_all_eq(t, max, i);
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
      if(bi == bp || pos - i == bp - bi || pos - i == bi - bp) {
        //@ not_consistent_monotonic(vs, pos, nat_of_int(pos - i - 1));
        return false;
      }
    }
    return true;
  }
  
  static int[] search(int[] board, int pos)
    //@ requires board != null &*& array_slice(board, 0, board.length, ?vs) &*& inrange(vs, board.length) == true &*& 0 <= pos && pos <= board.length &*& allconsistent(vs, nat_of_int(pos)) == true;
    /*@ ensures array_slice(board, 0, board.length, ?vs2) &*& inrange(vs2, board.length) == true &*& result == null  ? 
                  take(pos, vs) == take(pos, vs2) &*&
                  allconsistent(vs2, nat_of_int(pos)) == true &*&
                  inconsistent(vs2, nat_of_int(board.length), pos): 
                  result == board &*& allconsistent(vs2, nat_of_int(length(vs2))) == true; @*/
  {
    if(pos == board.length) {
      return board;
    } else {
      //@ close inconsistent(vs, zero, pos);
      for(int i = 0; i < board.length; i++) 
        //@ invariant 0 <= i &*& i <= board.length &*& array_slice(board, 0, board.length, ?vs2) &*& inrange(vs2, board.length) == true &*& take(pos, vs) == take(pos, vs2) &*& allconsistent(vs2, nat_of_int(pos)) == true &*& inconsistent(vs2, nat_of_int(i), pos);
      {
        board[pos] = i;
        //@ assert array_slice(board, 0, board.length, ?vs3);
        //@ take_append(take(pos, vs2), append(cons(i, nil), take(length(vs2) - pos - 1, tail(drop(pos, vs2)))), pos);
        //@ take_allconsistent(vs2, nat_of_int(pos));
        //@ append_allconsistent(take(pos, vs2), nat_of_int(pos), append(cons(i, nil), take(length(vs2) - pos - 1, tail(drop(pos, vs2)))));
        //@ inconsistent_take(vs2, nat_of_int(i), pos, vs3);
        //@ inrange_update(vs2, board.length, i, pos);
        //@ inrange_update_array(vs2, board.length, i, pos);        
        if(isConsistent(board, pos)) {
          //@ succ_int(pos);
          int[] s = search(board, pos + 1);
          if(s != null) {
            return s;
          }
          //@ assert array_slice(board, 0, board.length, ?vs4);
          //@ take_oke(vs3, vs4, pos);
          //@ inconsistent_take(vs2, nat_of_int(i), pos, vs3);
          //@ inconsistent_take(vs3, nat_of_int(i), pos, vs4);
          //@ succ_int(i);
          //@ nth_take(pos, pos + 1, vs4); 
          //@ update_nth(vs4, i, pos);
          //@ close inconsistent(vs4, (nat_of_int(i + 1)), pos);
        } else {
          //@ succ_int(i);
          //@ close inconsistent(vs3, (nat_of_int(i + 1)), pos);
        }
      }
      return null;
    }
  }
  
  static int[] startsearch(int[] board) 
    //@ requires board != null &*& array_slice(board, 0, board.length, ?vs) &*& inrange(vs, board.length) == true;
    //@ ensures array_slice(board, 0, board.length, ?vs2) &*& inrange(vs2, board.length) == true &*& result == null ? inconsistent(vs2, nat_of_int(board.length), 0) : result == board &*& allconsistent(vs2, nat_of_int(length(vs2))) == true;
  {
    return search(board, 0);
  }
  
  public static void main(String[] args) 
    //@ requires true;
    //@ ensures true;
  {
    int[] board = new int[2];
    //@ int length = board.length;
    //@ assert array_slice(board, 0, board.length, ?vs);
    //@ inrange_all_eq(vs, 2, 0);
    int[] res = startsearch(board);
      //@ assert array_slice(board, 0, length, ?vs2);
    if(res == null) {
      // we can prove from startsearch's postcondition that any board of size 2 is inconsistent
      int[] myboard = new int[2];
      myboard[0] = 0;
      myboard[1] = 1;
      //@ assert array_slice(board, 0, board.length, ?myvs);
      //@ inconsistent_take(vs2, nat_of_int(board.length), 0, myvs);
      //@ assert inconsistent(myvs, nat_of_int(myboard.length), 0);
    } else {
      //@ assert vs2 == cons(?p0, cons(?p1, nil));
      //@ succ_int(1);
      //@ succ_int(0);
      //@ assert nat_of_int(length(vs2)) == succ(succ(zero));
      /*@
      if (p0 < 1) {
          assert p0 == 0;
      } else {
          assert p0 == 1;
      }
      @*/
      /*@
      if (p1 < 1) {} else {}
      @*/
      assert false; // not reachable
    }
  }
}
