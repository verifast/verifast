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

lemma void take_one_more2<t>(list<t> vs, int i)
  requires 0 <= i && i < length(vs);
  ensures append(take(i, vs), cons(head(drop(i, vs)), nil)) == take(i + 1, vs);
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(i == 0) 
      {
      } else {
        take_one_more2(t, i - 1);
      }
  }
}

fixpoint boolean le(int x, int y) { return x <= y; }

fixpoint boolean forall_le(list<int> vs, int v) {
    return forall(vs, (le)(v));
}

lemma void forall_le_mono(list<int> vs, int v1, int v2)
  requires forall_le(vs, v1) && v2 <= v1;
  ensures forall_le(vs, v2) == true;
{
  switch (vs) {
    case nil:
    case cons(v0, vs0):
      forall_le_mono(vs0, v1, v2);
  }
}

lemma void store_take_drop<t>(list<t> xs, int index, t v)
  requires 0 <= index && index < length(xs);
  ensures update(index, v, xs) == append(take(index, xs), cons(v, drop(index + 1, xs)));
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

fixpoint boolean is_perm(list<int> xs, list<int> ys)
{
  switch(xs) {
    case nil: return ys == nil;
    case cons(h, t):
      return mem(h, ys) && is_perm(t, remove(h, ys));
  }
}

lemma_auto void is_perm_reflexive(list<int> xs) 
  requires true;
  ensures is_perm(xs, xs) == true;
{
  switch(xs) {
    case nil: 
    case cons(h, t): 
      switch(t) {
        case nil:
        case cons(h0, t0):
          is_perm_reflexive(t);
      }
  }
}

fixpoint int count<t>(list<t> xs, t x) {
  switch(xs) {
    case nil: return 0;
    case cons(h, t): return h == x ? 1 + count(t, x) : count(t, x);
  }
}

lemma void remove_mem(list<int> xs, int x, int y)
  requires x != y &*& mem(x, xs) == true;
  ensures mem(x, remove(y, xs)) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
     if(h == x) {
     } else {
       assert mem(x, t) == true;
       remove_mem(t, x, y);
     }
  }
}

lemma void mem_remove(list<int> xs, int x, int y)
  requires mem(x, remove(y, xs)) == true;
  ensures mem(x, xs) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
     if(h == x) {
     } else {
      if(h == y) {
      } else {
        mem_remove(t, x, y);
      }
     }
  }
}

lemma void remove_comm(list<int> xs, int x, int y) 
  requires true;
  ensures remove(x, remove(y, xs)) == remove(y, remove(x, xs));
{
  switch(xs) {
    case nil: 
    case cons(h, t):
      if(h == x) {
      } else {
        if(h == y) {
        } else {
          remove_comm(t, x, y);
        }
      }
  }
}

fixpoint boolean subset(list<int> xs, list<int> ys) {
  switch(xs) {
    case nil: return true;
    case cons(h, t): return mem(h, ys) && subset(t, ys);
  }
}

lemma void is_perm_mem(list<int> xs, list<int> ys, int x) 
  requires is_perm(xs, ys) == true &*& mem(x, xs) == true;
  ensures mem(x, ys) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(h == x) {
      } else {
         switch(ys) {
           case nil:
           case cons(h0, t0):
             if(h0 == x) {
             } else {
               is_perm_mem(t, remove(h, ys), x);
               mem_remove(ys, x, h);
             }
         }
      }
  }
}

lemma void is_perm_remove(list<int> xs, list<int> ys, int x)
  requires is_perm(xs, ys) == true;
  ensures is_perm(remove(x, xs), remove(x, ys)) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(x == h) {
      } else {
        remove_mem(ys, h, x); 
        remove_comm(ys, h, x);
        is_perm_remove(t, remove(h, ys), x);  
      }
  }
}


lemma void is_perm_transitive(list<int> xs, list<int> ys, list<int> zs)
  requires is_perm(xs, ys) == true &*& is_perm(ys, zs)== true;
  ensures is_perm(xs, zs) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      is_perm_mem(ys, zs, h);
      is_perm_remove(ys, zs, h);
      is_perm_transitive(t, remove(h, ys), remove(h, zs));
  }
}

lemma void insert_sorted_is_perm(list<int> xs, int v)
  requires true;
  ensures is_perm(insert_sorted(xs, v), cons(v, xs)) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(v < h) {
      } else {
        insert_sorted_is_perm(t, v);
      }
  }
}

lemma_auto void sort_is_perm(list<int> xs)
  requires true;
  ensures is_perm(sort(xs), xs) == true;
{
  switch(xs) {
   case nil:
   case cons(h, t):
     switch(t) {
       case nil:
       case cons(h0, t0):
         sort_is_perm(t);
         insert_sorted_is_perm(sort(t), h);
         is_perm_transitive(insert_sorted(sort(t), h),  cons(h, sort(t)), xs);        
     }
  }
}
@*/

class Comprehensions {
  public static int array_sum(int[] a)
    //@ requires array_slice(a, 0, a.length, ?vs);
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
      //@ take_one_more2(vs, i);
      i++;
    }
    return total;
  }
  
  public static int get(int[] a, int index)
    //@ requires array_slice(a, 0, a.length, ?vs) &*& 0 <= index &*& index < a.length;
    //@ ensures array_slice(a, 0, a.length, vs) &*& result == nth(index, vs);
  {
    int tmp = a[index];
    //@ length_drop(index, vs);
    //@ nth_drop(vs, index);
    return tmp;
  }
  
  public static void set(int[] a, int index, int v)
    //@ requires array_slice(a, 0, a.length, ?vs) &*& 0 <= index &*& index < a.length;
    //@ ensures array_slice(a, 0, a.length, update(index, v, vs));
  {
    a[index] = v;
  }

  
  public static int min(int[] a) 
    //@ requires array_slice(a, 0, a.length, ?vs) &*& vs != nil;
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
    //@ requires array_slice(a, start, a.length, ?vs) &*& vs != nil &*& length(vs) != 0;
    //@ ensures array_slice(a, start, a.length, vs) &*& start <= result &*& result < a.length &*& forall_le(vs, nth(result - start, vs)) == true;
  {
    int min = start;
    int j = start;
    while(j < a.length)
      //@ invariant start <= min &*& min < a.length && min <= j &*& j <= a.length &*& array_slice(a, start, a.length, vs) &*& forall_le(take(j - start, vs), nth(min - start, vs)) == true;
    {
      int tmp = a[j];
      int abc = 0;
      //@ length_drop(j - start, vs);
      int tmp2 = a[min];
      //@ length_drop(min - start, vs);
      //@ int old_min = min;
      if(tmp < tmp2) {
        min = j;
      }
      //@ take_one_more(j - start, vs);
      //@ drop_one_more(vs, j - start);
      //@ forall_append(take(j - start, vs), {nth(j - start, vs)}, (le)(nth(min - start, vs)));
      //@ forall_le_mono(take(j - start, vs), nth(old_min - start, vs), nth(min - start, vs));
      j++;
    }
    return min;
  }
  
    
  public static void insert_sorted(int[] a, int start)
    //@ requires array_slice(a, start, a.length, ?vs) &*& start < a.length;
    //@ ensures array_slice(a, start, a.length, insert_sorted(tail(vs), head(vs)));
  {
    if(start == a.length - 1) {
      //@ switch(vs) { case nil: case cons(h, t): }
      //@ switch(tail(vs)) { case nil: case cons(h, t): }
    } else {
      int tmp = a[start];
      int tmp2 = a[start + 1];
      //@ switch(vs) { case nil: case cons(h, t): }
      //@ switch(tail(vs)) { case nil: case cons(h, t): }
      if(tmp < tmp2) {
      } else {
        a[start + 1] = tmp;
        insert_sorted(a, start + 1);
        a[start] = tmp2;
      }
    }
  }
  
  public static void my_sort(int[] a, int start)
    //@ requires array_slice(a, start, a.length, ?vs);
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
  
  public static void sort(int[] a) 
    //@ requires array_slice(a, 0, a.length, ?vs);
    //@ ensures array_slice(a, 0, a.length, ?vs2) &*& is_sorted(vs2) == true &*& is_perm(vs2, vs) == true;
  {
    my_sort(a, 0);
  }
}