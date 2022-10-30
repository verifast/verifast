//@ #include "cryptogram.gh"

/*@

lemma_auto void cryptogram()
  requires [?f]cryptogram(?array, ?count, ?ccs, ?cg);
  ensures  [f]cryptogram(array, count, ccs, cg) &*&
           ccs == ccs_for_cg(cg) && cg_is_gen_or_pub(cg); 
{
  open [f]cryptogram(array, count, ccs, cg);
  close [f]cryptogram(array, count, ccs, cg);
}
 
lemma_auto void cryptogram_inv()
  requires [?f]cryptogram(?array, ?count, ?cs, ?cg);
  ensures  [f]cryptogram(array, count, cs, cg) &*& length(cs) == count;
{
  open [f]cryptogram(array, count, cs, cg);
  close [f]cryptogram(array, count, cs, cg);
}

lemma void cryptogram_limits(char *array)
  requires [?f]cryptogram(array, ?count, ?cs, ?cg) &*&
           pointer_within_limits(array) == true;
  ensures  [f]cryptogram(array, count, cs, cg) &*&
           pointer_within_limits(array + count) == true;
{
  open [f]cryptogram(array, count, cs, cg);
  crypto_chars_limits(array);
  close [f]cryptogram(array, count, cs, cg);
}

@*/
