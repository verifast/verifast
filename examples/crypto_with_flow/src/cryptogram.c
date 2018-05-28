//@ #include "../annotated_api/general_definitions/cryptogram.gh"

/*@

lemma_auto void cryptogram()
  requires [?f]cryptogram(?arr, ?count, ?cs, ?cg);
  ensures  [f]cryptogram(arr, count, cs, cg) &*&
           cs == chars_for_cg(cg) && cg_is_generated(cg);
{
  open [f]cryptogram(arr, count, cs, cg);
  close [f]cryptogram(arr, count, cs, cg);
}

lemma_auto void cryptogram_inv()
  requires [?f]cryptogram(?arr, ?count, ?cs, ?cg);
  ensures  [f]cryptogram(arr, count, cs, cg) &*& length(cs) == count;
{
  open [f]cryptogram(arr, count, cs, cg);
  close [f]cryptogram(arr, count, cs, cg);
}

lemma void cryptogram_limits(char *arr)
  requires [?f]cryptogram(arr, ?count, ?cs, ?cg) &*&
           true == ((char *)0 <= arr) &*& arr <= (char *)UINTPTR_MAX;
  ensures  [f]cryptogram(arr, count, cs, cg) &*&
           true == ((char *)0 <= arr) &*& arr + count <= (char *)UINTPTR_MAX;
{
  open [f]cryptogram(arr, count, cs, cg);
  crypto_chars_limits(arr);
  close [f]cryptogram(arr, count, cs, cg);
}

@*/
