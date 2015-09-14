//@ #include "../annotated_api/general_definitions/crypto_chars.gh"

/*@

lemma void optional_crypto_chars_inv(bool cc, char *array, int n, list<char> cs)
  requires [?f]optional_crypto_chars(cc, array, n, cs);
  ensures  [f]optional_crypto_chars(cc, array, n, cs) &*& length(cs) == n;
{
  open [f]optional_crypto_chars(cc, array, n, cs);
  if (cc)
  {
    crypto_chars_inv();
  }
  close [f]optional_crypto_chars(cc, array, n, cs);
}

lemma void cryptogram_inv()
  requires [?f]cryptogram(?array, ?n, ?cs, ?cg);
  ensures  [f]cryptogram(array, n, cs, cg) &*& length(cs) == n &*&
           cs == chars_for_cg(cg);
{
  open [f]cryptogram(array, n, cs, cg);
  crypto_chars_inv();
  close [f]cryptogram(array, n, cs, cg);
}

lemma void optional_crypto_chars_split(char *array, int offset)
  requires [?f]optional_crypto_chars(?cc, array, ?n, ?cs) &*& 0 <= offset &*& offset <= n;
  ensures  [f]optional_crypto_chars(cc, array, offset, take(offset, cs)) &*& 
           [f]optional_crypto_chars(cc, array + offset, n - offset, drop(offset, cs)) &*& 
           append(take(offset, cs), drop(offset, cs)) == cs;
{
  open [f]optional_crypto_chars(cc, array, n, cs);
  if (cc)
    crypto_chars_split(array, offset);
  else
    chars_split(array, offset);
}

lemma_auto void optional_crypto_chars_join(char *array)
  requires [?f]optional_crypto_chars(?cc, array, ?n, ?cs) &*& 
           [f]optional_crypto_chars(cc, array + n, ?n0, ?cs0);
  ensures  [f]optional_crypto_chars(cc, array, n + n0, append(cs, cs0));
{
  open [f]optional_crypto_chars(cc, array, n, cs);
  open [f]optional_crypto_chars(cc, array + n, n0, cs0);
  if (cc)
    crypto_chars_join(array);
  else
    chars_join(array);
}

@*/