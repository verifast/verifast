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

lemma void store_take_drop<t>(list<t> xs, int index, t v)
  requires 0 <= index && index < length(xs);
  ensures store(xs, index, v) == append(take(index, xs), cons(v, drop(index + 1, xs)));
{
  switch(xs) {
    case nil: 
    case cons(h, t): 
      if(index == 0) {
      } else { 
        store_take_drop(t, index - 1, v);
      }
  }
}

lemma void drop_one_more<t>(list<t> xs, int index)
  requires 0 <= index && index < length(xs);
  ensures drop(index, xs) == cons(nth(index, xs), drop(index + 1, xs));
{
  switch(xs) {
    case nil: 
    case cons(h, t): 
      if(index == 0) {
      } else { 
        drop_one_more(t, index - 1);
      }
  }
}

fixpoint list<int> insert_sorted(list<int> vs, int v) {
  switch(vs) {
    case nil: return cons(v, nil);
    case cons(h, t): return v < h ? cons(v, cons(h, t)) : cons(h, insert_sorted(t, v));
  }
}

fixpoint list<int> sort(list<int> vs) {
 switch(vs) {
   case nil: return nil;
   case cons(h, t): return insert_sorted(sort(t), h);
 }
}

fixpoint boolean is_sorted(list<int> vs) {
  switch(vs) {
    case nil: return true;
    case cons(h, t):
      return switch(t) { 
        case nil: return true; 
        case cons(h0, t0): return h <= h0 && is_sorted(t);
      };
  }
}

lemma void insert_sorted_preserves_is_sorted(list<int> vs, int v)
  requires is_sorted(vs) == true;
  ensures is_sorted(insert_sorted(vs, v)) == true;
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(v < h) {
      } else {
        switch(t) { case nil: case cons(h0, t0): };
        insert_sorted_preserves_is_sorted(t, v);
      }
  }
}

lemma_auto(is_sorted(sort(vs))) void sort_sorts(list<int> vs) 
  requires true;
  ensures is_sorted(sort(vs)) == true;
{
  switch(vs) {
    case nil:
    case cons(h, t): 
      switch(t) {
        case nil: 
        case cons(h0, t0):
          sort_sorts(t);
          insert_sorted_preserves_is_sorted(sort(t), h);
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
  
  public static void set(int[] a, int index, int v)
    //@ requires a != null &*& array_slice(a, 0, a.length, ?vs) &*& 0 <= index &*& index < a.length;
    //@ ensures array_slice(a, 0, a.length, store(vs, index, v));
  {
    a[index] = v;
    //@ drop_one_more(vs, index);
    //@ length_drop(index, vs);
    //@ nth_drop(vs, index);
    //@ store_take_drop(vs, index, v);
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
  
    
  public static void insert_sorted(int[] a, int start)
    //@ requires a != null &*& array_slice(a, start, a.length, ?vs) &*& start < a.length;
    //@ ensures array_slice(a, start, a.length, insert_sorted(tail(vs), head(vs)));
  {
    if(start == a.length - 1) {
      //@ switch(vs) { case nil: case cons(h, t): }
      //@ switch(tail(vs)) { case nil: case cons(h, t): }
    } else {
      int tmp = a[start];
      int tmp2 = a[start + 1];
      if(tmp < tmp2) {
      } else {
        a[start + 1] = tmp;
        insert_sorted(a, start + 1);
        a[start] = tmp2;
      }
    }
  }
  
  public static void my_sort(int[] a, int start)
    //@ requires a != null &*& array_slice(a, start, a.length, ?vs);
    //@ ensures array_slice(a, start, a.length, sort(vs));
  {
    if(start == a.length) {
      //@ switch(vs) { case nil: case cons(h, t): }
    } else {
      //@ switch(vs) { case nil: case cons(h, t): }
      my_sort(a, start + 1);
      insert_sorted(a, start);
    }
  }
  
  public static void sort(int[] a)     //@ requires a!= null &*& array_slice(a, 0, a.length, ?vs);    //@ ensures a != null &*& array_slice(a, 0, a.length, ?vs2) &*& is_sorted(vs2) == true;  {    my_sort(a, 0);
  }
}