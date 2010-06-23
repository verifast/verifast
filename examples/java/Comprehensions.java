/*@
fixpoint int sum(list<int> vs) {
  switch(vs) {
    case nil: return 0;
    case cons(h, t): return h + sum(t);
  }
}

lemma_auto(sum(append(xs, ys))) void sum_append(list<int> xs, list<int> ys) 
  requires true;
  ensures sum(append(xs, ys)) == sum(xs) + sum(ys);
{
  switch(xs) {
    case nil: 
    case cons(h, t): sum_append(t, ys);
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

fixpoint boolean forall_le(list<int> vs, int v) {
  switch(vs) {
    case nil: return true;
    case cons(h, t): return v <= h && forall_le(t, v);
  }
}

lemma void nth_drop<t>(list<t> vs, int index) 
  requires 0 <= index && index < length(vs);
  ensures nth(index, vs) == head(drop(index, vs));
{
  switch(vs) {
    case nil: 
    case cons(h, t):
      if(index == 0) {
      } else {
        nth_drop(t, index - 1);
      }
  }
}

@*/

class Comprehensions {
  public static int array_sum(int[] a)
    //@ requires a != null &*& array_slice(a, 0, a.length, ?vs);
    //@ ensures array_slice(a, 0, a.length, vs) &*& result == sum(vs);
  {
    int total = 0;
    int i = 0;
    while(i < a.length) 
      //@ invariant 0 <= i &*& i <= a.length &*& array_slice(a, 0, a.length, vs) &*& total == sum(take(i, vs));
    {
      int tmp = a[i];
      total = total + tmp;
      //@ length_drop(i, vs);
      //@ take_one_more(vs, i);
      i++;
    }
    return total;
  }
  
  public static int get(int[] a, int index)
    //@ requires a != null &*& array_slice(a, 0, a.length, ?vs) &*& 0 <= index &*& index < a.length;
    //@ ensures array_slice(a, 0, a.length, vs) &*& result == nth(index, vs);
  {
    int tmp = a[index];
    //@ length_drop(index, vs);
    //@ nth_drop(vs, index);
    return tmp;
  }
  
  public static int min(int[] a) 
    //@ requires a != null &*& array_slice(a, 0, a.length, ?vs) &*& vs != nil;
    //@ ensures array_slice(a, 0, a.length, vs) &*& mem(result, vs) == true && forall_le(vs, result);
  { 
    //@ switch(vs) { case nil:  case cons(h, t): }
    int tmp = indexOfMin(a, 0);
    //@ length_drop(tmp, vs);
    //@ nth_drop(vs, tmp);
    //@ mem_nth(tmp, vs);
    return a[tmp];
  }
  
  public static int indexOfMin(int[] a, int start) 
    //@ requires a != null &*& array_slice(a, start, a.length, ?vs) &*& vs != nil &*& length(vs) != 0;
    //@ ensures array_slice(a, start, a.length, vs) &*& start <= result &*& result < a.length &*& forall_le(vs, nth(result, vs))== true;
  {
    int min = start;
    int j = start;
    while(j < a.length) 
      //@ invariant start <= min &*& min < a.length && min <= j &*& j <= a.length &*& array_slice(a, start, a.length, vs) &*& forall_le(take(j - start, vs), nth(min, vs)) == true;
    {
      int tmp = a[j];
      int abc = 0;
      //@ length_drop(j - start, vs);
      int tmp2 = a[min];
      //@ length_drop(min - start, vs);
      if(tmp < tmp2) {
        min = j;
      }
    }
    return min;
  }
}