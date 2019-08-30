/*@
inductive bucket = bucket(int);

fixpoint bool truth_about_bucket(bucket b) {
  switch(b) {
    case bucket(x):
      return true;
  }
}

lemma void in_this_bucket_then_in_the_map<kt>(list<bucket > buckets, int n)
requires buckets != nil &*& // this is here for the switch
         0 <= n &*& n < length(buckets) &*&
         true == truth_about_bucket(nth(n, buckets));
ensures true;
{
  switch(buckets) {
    case nil:
    case cons(h,t):
      if (n != 0) {
        assert t != nil; // This line causes failure
      }
  }
}
@*/
