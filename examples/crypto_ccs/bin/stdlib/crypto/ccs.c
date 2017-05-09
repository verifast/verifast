//@ #include "ccs.gh"

/*@

lemma void public_cs_to_ccs(list<crypto_char> ccs)
  requires [_]public_ccs(ccs);
  ensures [_]is_forall_t<list<char> >(?forallcs) &*&
          true == exists_t<list<char> >(forallcs, (cs_to_ccs_eq)(ccs));
{ 
  open [_]public_ccs(ccs);
  get_forall_t<list<char> >();
  assert [_]is_forall_t<list<char> >(?forallcs);
  assert [_]exists(?cs) &*& ccs == cs_to_ccs(cs);
  if (!exists_t<list<char> >(forallcs, (cs_to_ccs_eq)(ccs)))
  {
    forall_t_elim(forallcs, (notf)((cs_to_ccs_eq)(cs_to_ccs(cs))), cs);
  }
}

lemma void cs_to_ccs_length(list<char> xs)
  requires true;
  ensures length(xs) == length(cs_to_ccs(xs));
{
  switch (xs)
  {
    case cons(x, xs0):
      cs_to_ccs_length(xs0);
    case nil:
  }
}

lemma void cs_to_ccs_append(list<char> xs, list<char> ys)
  requires true;
  ensures append(cs_to_ccs(xs), cs_to_ccs(ys)) ==
          cs_to_ccs(append(xs, ys));
{
  switch (xs)
  {
    case cons(x, xs0):
      cs_to_ccs_append(xs0, ys);
    case nil:
  }
}

lemma void cs_to_ccs_take(int i, list<char> xs)
  requires true;
  ensures take(i, cs_to_ccs(xs)) == cs_to_ccs(take(i, xs));
{
  switch (xs)
  {
    case cons(x, xs0):
      cs_to_ccs_take(i - 1, xs0);
    case nil:
  }
}

lemma void cs_to_ccs_drop(int i, list<char> xs)
  requires true;
  ensures drop(i, cs_to_ccs(xs)) == cs_to_ccs(drop(i, xs));
{
  switch (xs)
  {
    case cons(x, xs0):
      cs_to_ccs_drop(i - 1, xs0);
    case nil:
  }
}

lemma void c_to_cc_inj(char c1, char c2)
  requires true;
  ensures  true == ((c_to_cc(c1) == c_to_cc(c2)) == (c1 == c2));
{
  fixpoint(secret_coin_tosses, char) cc1, cc2;
  secret_coin_tosses sampling;
  cc1 = (crypto_char_const)(c1);
  cc2 = (crypto_char_const)(c2);
  cc1(sampling);
  cc2(sampling);
}

lemma void cs_to_ccs_inj(list<char> cs1, list<char> cs2)
  requires true;
  ensures  true == ((cs1 == cs2) == (cs_to_ccs(cs1) == cs_to_ccs(cs2)));
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

@*/