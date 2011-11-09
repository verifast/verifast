

class Problem1 {
  static void two_way_sort(boolean[] a) 
    //@ requires array_slice(a, 0, a.length, ?vs);
    //@ ensures array_slice(a, 0, a.length, ?vs2);
  {
    int i = 0;
    int j = a.length - 1;
    while(i <= j) 
      /*@ invariant 0 <= i && i <= a.length &*& -1 <= j &*& j < a.length &*& 
          array_slice(a, 0, a.length, ?xs); @*/ // &*&
          //all_eq(take(i, xs), false) == true &*&
          //all_eq(drop(j + 1, xs), true) == true; 
    {
      if(! a[i]) {
        i++;
      } else if (a[j]) {
        j--;
      } else {
        swap(a, i, j);
        i++;
        j--;
      }
    }
  }
}