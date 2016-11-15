//@ #include "../annotated_api/general_definitions/crypto_chars.gh"

/*@

lemma void cs_to_ccs_split(list<char> xs, list<char> ys)
  requires true;
  ensures append(cs_to_ccs(xs), cs_to_ccs(ys)) ==
          cs_to_ccs(append(xs, ys));
{
  switch (xs)
  {
    case cons(x, xs0):
      cs_to_ccs_split(xs0, ys);
    case nil:
  }
}

lemma void c_to_cc_inj(char c1, char c2)
  requires c_to_cc(c1) == c_to_cc(c2);
  ensures  c1 == c2;
{
  fixpoint(fixpoint(int, list<char>), char) cc1, cc2;
  cc1 = (c_to_cc_const)(c1);
  cc2 = (c_to_cc_const)(c2);
  assert cc1(chars_for_cg_dummy) == cc2(chars_for_cg_dummy);
}

lemma void cs_to_ccs_inj(list<char> cs1, list<char> cs2)
  requires cs_to_ccs(cs1) == cs_to_ccs(cs2);
  ensures  cs1 == cs2;
{
  switch(cs1)
  {
    case cons(c1, cs1'):
      switch(cs2)
      {
        case cons(c2, cs2'):
          cs_to_ccs_inj(cs1', cs2');
          c_to_cc_inj(c1, c2);
        case nil:
      }
    case nil:
     switch(cs2)
     {
       case cons(c2, cs2'):
       case nil:
     }
  }
}

lemma void cs_to_ccs_chars(char* b, list<char> cs2)
  requires [?f]chars(b, ?c, ?cs1) &*&
           cs_to_ccs(cs1) == cs_to_ccs(cs2);
  ensures  [f]chars(b, c, cs2);
{
  cs_to_ccs_inj(cs1, cs2);
}

lemma void cs_to_ccs_crypto_chars(char *array, list<char> cs)
  requires [?f]crypto_chars(?kind, array, ?n, cs_to_ccs(cs)) &*&
           col || kind == normal;
  ensures  [f]chars(array, n, cs);
{
  crypto_chars_to_chars(array, n);
  assert [f]chars(array, n, ?cs');
  cs_to_ccs_inj(cs, cs');
}

lemma void cs_to_ccs_length(list<char> cs)
  requires true;
  ensures  length(cs) == length(cs_to_ccs(cs));
{
  switch(cs)
  {
    case cons(c0, cs0):
      cs_to_ccs_length(cs0);
    case nil:
  }
}

@*/
