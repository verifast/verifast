/*@
fixpoint boolean forall<t>(list<t> xs, fixpoint(t, boolean) p) {
  switch(xs) {
    case nil: return true;
    case cons(h, t): return p(h) && forall(t, p);
  }
}
lemma void not_forall<t>(list<t> xs, fixpoint(t, boolean) p, int i);
  requires 0<=i &*& i < length(xs) &*& ! p(nth(i, xs));
  ensures ! forall(xs, p);

lemma_auto void take_nth<t>(list<t> xs, int i, int j);
  requires 0<=i &*& i < j &*& j <= length(xs);
  ensures nth(i, take(j, xs)) == nth(i, xs);
fixpoint list<any> zip<t1, t2>(list<t1> xs, list<t2> ys) {
  switch(xs) {
    case nil: return nil;
    case cons(xh, xt):
      return switch(ys) {
        case nil: return nil;
        case cons(yh, yt): return cons((any) pair(xh, yh), zip(xt, yt));
      };
  }
}


fixpoint boolean safe(unit u, list<int> vs, int pos, int bp, int bq) {
  switch(u) {
    case unit: return bp != bq;// && bp - nth(q, vs) != pos - q;
  }
}

lemma void take_one_more<t>(list<t> vs, int i)
  requires 0 <= i && i < length(vs);
  ensures append(take(i, vs), cons(head(drop(i, vs)), nil)) == take(i + 1, vs);
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(i == 0) 
      {
      } else {
        take_one_more(t, i - 1);
      }
  }
}

lemma void nth_head_drop<t>(list<t> vs, int i)
  requires 0 <= i && i < length(vs);
  ensures head(drop(i, vs)) == nth(i, vs);
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(i == 0) 
      {
      } else {
        nth_head_drop(t, i - 1);
      }
  }
}

lemma void append_forall<t>(list<t> vs1, list<t> vs2, fixpoint(t, boolean) p)
  requires forall(vs1, p) && forall(vs2, p);
  ensures forall(append(vs1, vs2), p) == true;
{
  switch(vs1) {
    case nil:
    case cons(h, t): append_forall(t, vs2, p);
  }
}


@*/

class NQueens {   
  public static boolean isConsistent(int[] board, int pos) 
    //@ requires board != null &*& array_slice(board, 0, board.length, ?vs) &*& 0 <= pos &*& pos < board.length;
    //@ ensures board != null &*& array_slice(board, 0, board.length, vs) &*& forall(take(pos, vs), (safe)(unit, vs, pos, nth(pos, vs))) == result;
  {
    int bp = board[pos];      
    for(int q = 0; q < pos; q++) 
      //@ invariant 0 <= q &*& q <= pos &*& array_slice(board, 0, board.length, vs) &*& forall(take(q, vs), (safe)(unit, vs, pos, bp)) == true;
    {
      int bq = board[q];
      //@ assert bq == nth(q, vs);
      if(bq == bp /*|| (bp - bq == pos - q) || (bp - bq == pos - q)*/) {
        //@ take_nth(vs, q, pos);
        //@ assert bq == nth(q, vs);
        //@ not_forall(take(pos, vs), (safe)(unit, vs, pos, bp), q);
        return false;
      }
      //@ take_one_more(vs, q);
      //@ nth_head_drop(vs, q);
      //@ append_forall(take(q, vs), cons(nth(q, vs), nil), (safe)(unit, vs, pos, bp));
    }

    return true;
  }

  /*public static int[] search(int[] board, int pos) 
    //@ requires board != null &*& array_slice(board, 0, board.length, ?vs) &*& 0 <= pos &*& pos <= board.length &*& forall(take(pos-1, vs), (safe)(unit, pos - 1, nth(pos - 1, vs))) == true;
    //@ ensures result == null ? array_slice(board, 0, board.length, ?vs2) : result == board &*& array_slice(result, 0, board.length, ?vs2) &*&  forall(take(board.length - 1, vs2), (safe)(unit, board.length - 1, nth(board.length - 1, vs2))) == true;
  {
    if(pos == board.length) {
      return board;
    }

    for(int i = 0; i < pos; i++) 
      //@ invariant array_slice(board, 0, board.length, ?vs3);
    {
      board[pos] = i;
      if(isConsistent(board, pos)) {
        int[] s = search(board, pos + 1);
        if(s != null) {
          return s;
        }
      }
    }
    return null;
  }*/
}