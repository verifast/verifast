//@ #include "memcmp.gh"

/*@

lemma void memcmp_match(list<memcmp_part> l, list<memcmp_part> l1, 
                                             list<memcmp_part> l2)
  requires memcmp_match(l, l1) && memcmp_match(l, l2);
  ensures  true == memcmp_match(l1, l2);
{
  switch(l)
  {
    case cons(p, l0):
      switch(l1)
      {
        case cons(p1, l01):
          switch(l2)
          {
            case cons(p2, l02):
              memcmp_match(l0, l01, l02);
            case nil:
          }
        case nil:
      }
    case nil:
  }
}

lemma void memcmp_append0(list<memcmp_part> l1, list<memcmp_part> l2)
  requires [_]memcmp_region(l1, ?ccs1) &*& [_]memcmp_region(l2, ?ccs2);
  ensures  [_]memcmp_region(append(l1, l2), append(ccs1, ccs2));
{
  switch(l1)
  {
    case nil:
      open [_]memcmp_region(l1, ccs1);
      open [_]memcmp_region(l2, ccs2);
    case cons(p, l_rest):
      open [_]memcmp_region(l1, ccs1);
      open [_]memcmp_region(l2, ccs2);
      list<crypto_char> ccs_curr = memcmp_part_ccs(p);
      list<crypto_char> ccs_rest = drop(length(ccs_curr), ccs1);
      take_length_bound(length(ccs_curr), ccs1);
      append_drop_take(ccs1, length(ccs_curr));
      take_append(length(ccs_curr), ccs1, ccs2);
      drop_append(length(ccs_curr), ccs_curr, append(ccs_rest, ccs2));
      append_assoc(ccs_curr, ccs_rest, ccs2);
      assert ccs1 == append(ccs_curr, ccs_rest);
      assert append(l1, l2) == cons(p, append(l_rest, l2));
      assert append(ccs1, ccs2) == append(ccs_curr, append(ccs_rest, ccs2));
      MEMCMP_REGION(l_rest, ccs_rest);
      memcmp_append0(l_rest, l2);
      open [_]memcmp_region(append(l_rest, l2), append(ccs_rest, ccs2));
      MEMCMP_REGION(append(l1, l2), append(ccs1, ccs2));
  }
}

lemma void memcmp_append(list<crypto_char> ccs1, list<crypto_char> ccs2)
  requires [_]memcmp_region(?l1, ccs1) &*& [_]memcmp_region(?l2, ccs2);
  ensures  [_]memcmp_region(append(l1, l2), append(ccs1, ccs2));
{
  memcmp_append0(l1, l2);
}
@*/
  
