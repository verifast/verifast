//@# include "interval.gh"

/*@


lemma void mem_interval_core(int x, int lower, int upper, nat diff)
  requires lower <= upper &*& int_of_nat(diff) == upper - lower;
  ensures mem(x, interval_core(lower, upper, diff)) == (lower <= x && x < upper);
{
  switch(diff) {
    case zero:
    case succ(diff0):
      mem_interval_core(x, lower + 1, upper, diff0);
  }
}

lemma void mem_interval(int x, int lower, int upper)
  requires true;
  ensures mem(x, interval(lower, upper)) == (lower <= x && x < upper);
{
  if(lower < upper) {
    mem_interval_core(x, lower, upper, nat_of_int(upper - lower));
  }
}

lemma void distinct_interval_core(int lower, int upper, nat diff)
  requires lower <= upper &*& int_of_nat(diff) == upper - lower;
  ensures distinct(interval_core(lower, upper, diff)) == true;
{
  switch(diff) {
    case zero:
    case succ(diff0):
      distinct_interval_core(lower + 1, upper, diff0);
      mem_interval_core(lower, lower + 1, upper, diff0);
  }
}

lemma_auto void distinct_interval(int lower, int upper)
  requires true;
  ensures distinct(interval(lower, upper)) == true;
{
  if(lower < upper) {
    distinct_interval_core(lower, upper, nat_of_int(upper - lower));
  }
}

lemma void empty_interval(int lower)
  requires true;
  ensures interval(lower, lower) == nil;
{
}

lemma void cons_interval(int lower, int upper)
  requires lower < upper;
  ensures interval(lower, upper) == cons(lower, interval(lower+1, upper));
{
  int_of_nat(nat_of_int(upper - lower));
  switch(nat_of_int(upper - lower)) { 
    case zero:
    case succ(diff0) :  
  }
}

lemma void interval_split(int x, int lower, int upper)
  requires lower <= x && x <= upper;
  ensures interval(lower, upper) == append(interval(lower, x), interval(x, upper));
{
  int i = x - lower;
  while(i > 0) 
    invariant 0 <= i &*& i <= x - lower &*& interval(lower + i, upper) == append(interval(lower + i, x), interval(x, upper));
    decreases i;
  {
    cons_interval(lower + i - 1, x);
    cons_interval(lower + i - 1, upper);
    i--;
  }
}
  
lemma void remove_first_interval(int lower, int upper)
  requires lower < upper;
  ensures remove(lower, interval(lower, upper)) == interval(lower + 1, upper);
{
  cons_interval(lower, upper);
}
@*/