#include "item_constraints.h"

/*@

lemma void well_formed_upper_bound(list<char> cs, nat upper_bound1, 
                                                  nat upper_bound2)
  requires true == well_formed(cs, upper_bound1) &*&
           length(cs) <= int_of_nat(upper_bound2);
  ensures  true == well_formed(cs, upper_bound2);
{
  switch(upper_bound1)
  { 
    case zero: assert false; 
    case succ(n_ub1):
      switch(upper_bound2)
      { 
        case zero: assert false; 
        case succ(n_ub2):
          if (head(cs) == 'b')
          {
            assert cs == cons('b', ?cs0);
            int length_f_cs, length_s_cs;
            list<char> p_cs, f_cs, s_cs;

            if (INT_MIN <= head(tail(cs)) && head(tail(cs)) <= INT_MAX)
            {
              length_f_cs = int_of_chars(take(sizeof(int), tail(cs)));
              length_s_cs = length(cs) - 1 - sizeof(int) - length_f_cs;
              p_cs = drop(1 + sizeof(int), cs);
              f_cs = take(length_f_cs, p_cs);
              s_cs = drop(length_f_cs, p_cs);

              length_drop(1 + sizeof(int), cs);
              length_take(length_f_cs, p_cs);
              length_drop(length_f_cs, p_cs);

              assert cs0 == append(chars_of_int(length_f_cs),  
                                   append(f_cs, s_cs));
            }
            else
            {
              length_f_cs = head(tail(cs));
              length_s_cs = length(cs) - 2 - length_f_cs;
              p_cs = drop(2, cs);
              f_cs = take(length_f_cs, p_cs);
              s_cs = drop(length_f_cs, p_cs);
              
              length_drop(2, cs);
              length_take(length_f_cs, p_cs);
              length_drop(length_f_cs, p_cs);
              
              assert cs0 == cons(length_f_cs, ?cs1);
              assert cs1 == append(f_cs, s_cs);
            }
            
            assert true == well_formed(f_cs, n_ub1);
            assert true == well_formed(s_cs, n_ub1);
            
            well_formed_upper_bound(f_cs, n_ub1, n_ub2);
            well_formed_upper_bound(s_cs, n_ub1, n_ub2);
            
            assert true == well_formed(f_cs, n_ub2);
            assert true == well_formed(s_cs, n_ub2);
            assert true == well_formed(cs, upper_bound2);
          }
      }
  }
}

lemma void tag_for_dummy_item(item i, char t)
  requires valid_tag(t) &&
           i == dummy_item_for_tag(t);
  ensures  t == tag_for_item(i);
{
  switch (i)
  {
    case data_item(cs0):
      assert t == tag_for_item(i);
    case pair_item(f0, s0):
      assert t == tag_for_item(i);
    case nonce_item(p0, c0, inc0):
      assert t == tag_for_item(i);
    case hash_item(pay0):
      assert t == tag_for_item(i);
    case symmetric_key_item(p0, c0):
      assert t == tag_for_item(i);
    case public_key_item(p0, c0):
      assert t == tag_for_item(i);
    case private_key_item(p0, c0):
      assert t == tag_for_item(i);
    case hmac_item(p0, c0, pay0):
      assert t == tag_for_item(i);
    case symmetric_encrypted_item(p0, c0, pay0, ent0):
      assert t == tag_for_item(i);
    case asymmetric_encrypted_item(p0, c0, pay0, ent0):
      assert t == tag_for_item(i);
    case asymmetric_signature_item(p0, c0, pay0, ent0):
      assert t == tag_for_item(i);
  }
}

lemma void well_formed_valid_tag(list<char> cs, nat len)
  requires true == well_formed(cs, len);
  ensures  true == valid_tag(head(cs));
{
  switch(len) {case succ(n): case zero:}
}

// Redux ...
lemma void well_formed_pair_item_2(list<char> cs, 
                                   list<char> cs_f, list<char> cs_s,
                                   nat n)
  requires length(cs) > 0 && length(cs) <= INT_MAX &*&
           true == valid_tag(head(cs)) &*&
           head(cs) == 'b' &*&
           length(cs) > 2 &*&
           INT_MIN <= head(tail(cs)) && head(tail(cs)) <= INT_MAX &*&
           int_of_chars(take(sizeof(int), tail(cs))) > 0 &*&
           length(cs) > 
                1 + sizeof(int) + int_of_chars(take(sizeof(int), tail(cs))) &*&
           cs_f == take(int_of_chars(take(sizeof(int), tail(cs))),
                        drop(1 + sizeof(int), cs)) &*&
           cs_s == drop(int_of_chars(take(sizeof(int), tail(cs))),
                            drop(1 + sizeof(int), cs)) &*&
           true == well_formed(cs_f, n) &*&
           true == well_formed(cs_s, n) &*&
           succ(n) == nat_length(cs);
  ensures  true == well_formed(cs, nat_length(cs));
{
}

lemma void well_formed_pair_item(list<char> cs, 
                                 list<char> cs_f, list<char> cs_s)
  requires length(cs) > 0 &*& length(cs) <= INT_MAX &*&
           cs == cons('b', ?cs0) &*&
           cs0 == append(chars_of_unbounded_int(length(cs_f)), 
                        append(cs_f, cs_s)) &*&
           well_formed(cs_f, nat_length(cs_f)) &&
           well_formed(cs_s, nat_length(cs_s));
  ensures  true == well_formed(cs, nat_length(cs));
{
  switch(nat_length(cs))
  {
    case succ(n):
      length_equals_nat_length(cs);
      well_formed_upper_bound(cs_f, nat_length(cs_f), n);
      well_formed_upper_bound(cs_s, nat_length(cs_s), n);
      assert true == well_formed(cs_f, n);
      assert true == well_formed(cs_s, n);
      take_append(length(cs_f), cs_f, cs_s);
      drop_append(length(cs_f), cs_f, cs_s);
      
      if (INT_MIN <= length(cs_f) && length(cs_f) <= INT_MAX)
      {
        take_append(sizeof(int), chars_of_int(length(cs_f)), 
                                  append(cs_f, cs_s));
        drop_append(sizeof(int), chars_of_int(length(cs_f)), 
                                  append(cs_f, cs_s));
        length_take(int_of_chars(take(sizeof(int), tail(cs))), 
                    append(cs_f, cs_s));
        head_append(chars_of_int(length(cs_f)), append(cs_s, cs_f));
        switch(chars_of_int(length(cs_f))) {case cons(c1, cs1): case nil:}
        chars_of_int_char_in_bounds(head(tail(cs)), length(cs_f));
        well_formed_pair_item_2(cs, cs_f, cs_s, n);
      }
      else
      {
        assert head(tail(cs)) > 0;
        assert length(cs) > 2 + head(tail(cs));
        assert take(head(tail(cs)), drop(2, cs)) == cs_f;
        assert drop(head(tail(cs)), drop(2, cs)) == cs_s;
      }
    case zero:
      assert false;
  }
}

#define ITEM_CONSTRAINTS_NO_COLLISION_WELL_FORMED \
  open [_]item_constraints_no_collision(i1, cs, pub); \
  close well_formed_item_chars(i2)(cs); \
  leak well_formed_item_chars(i2)(cs);
      
lemma void item_constraints_no_collision_well_formed(item i1, item i2)
  requires [_]item_constraints_no_collision(i1, ?cs, ?pub);
  ensures  [_]well_formed_item_chars(i2)(cs);
{
  switch(i1)
  {
    case data_item(d0):
      ITEM_CONSTRAINTS_NO_COLLISION_WELL_FORMED
    case pair_item(f0, s0):
      open [_]item_constraints_no_collision(i1, cs, pub);
      assert [_]item_constraints_no_collision(f0, ?cs_f0, pub);
      assert [_]item_constraints_no_collision(s0, ?cs_s0, pub);
      assert cs == cons('b', ?cs0);
      assert cs0 == append(chars_of_unbounded_int(length(cs_f0)), 
                           append(cs_f0, cs_s0));
                           
      item_constraints_no_collision_well_formed(f0, f0);
      open [_]well_formed_item_chars(f0)(cs_f0);
      item_constraints_no_collision_well_formed(s0, s0);
      open [_]well_formed_item_chars(s0)(cs_s0);
      assert true == well_formed(cs_f0, nat_length(cs_f0));
      assert true == well_formed(cs_s0, nat_length(cs_s0));
      well_formed_pair_item(cs, cs_f0, cs_s0);
      close well_formed_item_chars(i2)(cs);
      leak well_formed_item_chars(i2)(cs);
    case nonce_item(p0, c0, inc0):
      ITEM_CONSTRAINTS_NO_COLLISION_WELL_FORMED
    case hash_item(pay0):
      ITEM_CONSTRAINTS_NO_COLLISION_WELL_FORMED
    case symmetric_key_item(p0, c0):
      ITEM_CONSTRAINTS_NO_COLLISION_WELL_FORMED
    case public_key_item(p0, c0):
      ITEM_CONSTRAINTS_NO_COLLISION_WELL_FORMED
    case private_key_item(p0, c0):
      ITEM_CONSTRAINTS_NO_COLLISION_WELL_FORMED
    case hmac_item(p0, c0, pay0):
      ITEM_CONSTRAINTS_NO_COLLISION_WELL_FORMED
    case symmetric_encrypted_item(p0, c0, pay0, ent0):
      ITEM_CONSTRAINTS_NO_COLLISION_WELL_FORMED
    case asymmetric_encrypted_item(p0, c0, pay0, ent0):
      ITEM_CONSTRAINTS_NO_COLLISION_WELL_FORMED
    case asymmetric_signature_item(p0, c0, pay0, ent0):
      ITEM_CONSTRAINTS_NO_COLLISION_WELL_FORMED
  }
}

lemma void item_constraints_well_formed(item i1, item i2)
  requires [_]item_constraints(?b1, i1, ?cs, ?pub);
  ensures  [_]well_formed_item_chars(i2)(cs);
{
  open [_]item_constraints(b1, i1, cs, pub);
  close well_formed_item_chars(i2)(cs);
  leak well_formed_item_chars(i2)(cs);
}

#define ITEM_CONSTRAINTS_NO_COLLISION_SURJECTIVE(CG1, CG2) \
  open [_]item_constraints_no_collision(i, cs1, pub); \
  assert [_]item_constraints_no_collision(pay1, ?cs_pay1, pub); \
  item_constraints_no_collision_well_formed(pay1, i); \
  assert [_]well_formed_item_chars(i)(cs_pay1); \
  \
  open [_]item_constraints_no_collision(i, cs2, pub); \
  assert [_]item_constraints_no_collision(pay1, ?cs_pay2, pub); \
  item_constraints_no_collision_well_formed(pay1, i); \
  assert [_]well_formed_item_chars(i)(cs_pay2); \
  \
  item_constraints_no_collision_surjective(cs_pay1, cs_pay2, pay1); \
  polarssl_cryptogram cg1 = CG1; \
  polarssl_cryptogram cg2 = CG2; \
  if (!collision_in_run()) \
    polarssl_chars_for_cryptogram_injective(cg1, cg2);
                              
lemma void item_constraints_no_collision_surjective(list<char> cs1, 
                                                    list<char> cs2, item i)
  requires true == well_formed_item(i) &*&
           [_]item_constraints_no_collision(i, cs1, ?pub) &*&
           [_]item_constraints_no_collision(i, cs2, pub);
  ensures  collision_in_run() ? true : cs1 == cs2;
{
  switch(i)
  {
    case data_item(d0):
      open [_]item_constraints_no_collision(i, cs1, pub);
      open [_]item_constraints_no_collision(i, cs2, pub);
    case pair_item(f0, s0):
      open [_]item_constraints_no_collision(i, cs1, pub);
      assert [_]item_constraints_no_collision(f0, ?cs_f1, pub);
      assert [_]item_constraints_no_collision(s0, ?cs_s1, pub);
      open [_]item_constraints_no_collision(i, cs2, pub);
      assert [_]item_constraints_no_collision(f0, ?cs_f2, pub);
      assert [_]item_constraints_no_collision(s0, ?cs_s2, pub);
      item_constraints_no_collision_surjective(cs_f1, cs_f2, f0);
      item_constraints_no_collision_surjective(cs_s1, cs_s2, s0);
    case nonce_item(p0, c0, inc0):
      open [_]item_constraints_no_collision(i, cs1, pub);
      open [_]item_constraints_no_collision(i, cs2, pub);
    case hash_item(pay0):
      switch(pay0)
      {
        case some(pay1):
          ITEM_CONSTRAINTS_NO_COLLISION_SURJECTIVE(
            polarssl_hash(cs_pay1),
            polarssl_hash(cs_pay2)
          )
        case none:
          assert false;
      }
    case symmetric_key_item(p0, c0):
      open [_]item_constraints_no_collision(i, cs1, pub);
      open [_]item_constraints_no_collision(i, cs2, pub);
    case public_key_item(p0, c0):
      open [_]item_constraints_no_collision(i, cs1, pub);
      open [_]item_constraints_no_collision(i, cs2, pub);
    case private_key_item(p0, c0):
      open [_]item_constraints_no_collision(i, cs1, pub);
      open [_]item_constraints_no_collision(i, cs2, pub);
    case hmac_item(p0, c0, pay0):
      switch(pay0)
      {
        case some(pay1):
          ITEM_CONSTRAINTS_NO_COLLISION_SURJECTIVE(
            polarssl_hmac(p0, c0, cs_pay1),
            polarssl_hmac(p0, c0, cs_pay2)
          )
        case none:
          assert false;
      }
    case symmetric_encrypted_item(p0, c0, pay0, ent0):
      switch(pay0)
      {
        case some(pay1):
          open [_]item_constraints_no_collision(i, cs1, pub);
          assert [_]item_constraints_no_collision(pay1, ?cs_pay1, pub);
          assert [_]symmetric_encryption_entropy(i)(?mac1, ?iv1);
          assert drop(GCM_ENT_SIZE, ent0) == 
                                          cons(length(mac1), append(mac1, iv1));
          item_constraints_no_collision_well_formed(pay1, i);
          assert [_]well_formed_item_chars(i)(cs_pay1);
          
          open [_]item_constraints_no_collision(i, cs2, pub);
          assert [_]item_constraints_no_collision(pay1, ?cs_pay2, pub);
          assert [_]symmetric_encryption_entropy(i)(?mac2, ?iv2);
          assert drop(GCM_ENT_SIZE, ent0) == 
                                          cons(length(mac2), append(mac2, iv2));
          item_constraints_no_collision_well_formed(pay1, i);
          assert [_]well_formed_item_chars(i)(cs_pay2);

          assert length(mac1) == length(mac2);
          take_append(length(mac1), mac1, iv1);
          take_append(length(mac2), mac2, iv2);
          drop_append(length(mac1), mac1, iv1);
          drop_append(length(mac2), mac2, iv2);
          assert mac1 == mac2;
          assert iv1 == iv2;
          item_constraints_no_collision_surjective(cs_pay1, cs_pay2, pay1);
          polarssl_cryptogram cg1 = 
                            polarssl_auth_encrypted(p0, c0, mac1, cs_pay1, iv1);
          polarssl_cryptogram cg2 = 
                            polarssl_auth_encrypted(p0, c0, mac2, cs_pay2, iv2);
          if (!collision_in_run())
            polarssl_chars_for_cryptogram_injective(cg1, cg2);
          assert cs1 == cons('i', ?cs10);
          assert cs2 == cons('i', ?cs20);           
          append_take_drop_n(cs10, GCM_ENT_SIZE);
          append_take_drop_n(cs20, GCM_ENT_SIZE);
        case none:
          assert false;
      }
    case asymmetric_encrypted_item(p0, c0, pay0, ent0):
      switch(pay0)
      {
        case some(pay1):
          ITEM_CONSTRAINTS_NO_COLLISION_SURJECTIVE(
            polarssl_asym_encrypted(p0, c0, cs_pay1, ent0),
            polarssl_asym_encrypted(p0, c0, cs_pay2, ent0)
          )
        case none:
          assert false;
      }
    case asymmetric_signature_item(p0, c0, pay0, ent0):
      switch(pay0)
      {
        case some(pay1):
          ITEM_CONSTRAINTS_NO_COLLISION_SURJECTIVE(
            polarssl_asym_signature(p0, c0, cs_pay1, ent0),
            polarssl_asym_signature(p0, c0, cs_pay2, ent0)
          )
        case none:
          assert false;
      }
  }
}

lemma void item_constraints_surjective(list<char> cs1, list<char> cs2, item i)
  requires true == well_formed_item(i) &*&
           [_]item_constraints(?b1, i, cs1, ?pub) &*&
           [_]item_constraints(?b2, i, cs2, pub);
  ensures  collision_in_run() ? true : cs1 == cs2;
{
  open [_]item_constraints(b1, i, cs1, pub);
  open [_]item_constraints(b2, i, cs2, pub);
    
  if (!b1 && !b2)
    item_constraints_no_collision_surjective(cs1, cs2, i);
}

#define ITEM_CONSTRAINTS_NO_COLLISION_INJEVTIVE_NONE_PAYLOAD(CG) \
  open [_]ill_formed_item_chars(i2)(?cs_pay2); \
  polarssl_cryptogram cg2 = CG; \
  assert cs_cg == polarssl_chars_for_cryptogram(cg2); \
  polarssl_chars_for_cryptogram_injective(cg1, cg2); \
  assert collision_in_run() ? true : i1 == i2; \

#define ITEM_CONSTRAINTS_NO_COLLISION_INJEVTIVE_SOME_PAYLOAD(CG) \
  open [_]well_formed_item_chars(i2)(?cs_pay2); \
  polarssl_cryptogram cg2 = CG; \
  polarssl_chars_for_cryptogram_injective(cg1, cg2); \
  if (!collision_in_run) \
  { \
    item_constraints_no_collision_injective(cs_pay1, pay1_, pay2_); \
    assert i1 == i2; \
  }

#define ITEM_CONSTRAINTS_NO_COLLISION_INJEVTIVE_PAYLOAD_SWITCH(CG) \
  switch(pay2) \
  { \
    case some(pay2_): \
      ITEM_CONSTRAINTS_NO_COLLISION_INJEVTIVE_SOME_PAYLOAD(CG) \
    case none: \
      ITEM_CONSTRAINTS_NO_COLLISION_INJEVTIVE_NONE_PAYLOAD(CG) \
  }

#define ITEM_CONSTRAINTS_NO_COLLISION_INJEVTIVE_PAYLOAD_DOUBLE_SWITCH(CG1, CG2) \
  switch(pay1) \
  { \
    case some(pay1_): \
      open [_]well_formed_item_chars(i1)(?cs_pay1); \
      polarssl_cryptogram cg1 = CG1; \
      assert cs_cg == polarssl_chars_for_cryptogram(cg1); \
      ITEM_CONSTRAINTS_NO_COLLISION_INJEVTIVE_PAYLOAD_SWITCH(CG2) \
    case none: \
      open [_]ill_formed_item_chars(i1)(?cs_pay1); \
      polarssl_cryptogram cg1 = CG1; \
      assert cs_cg == polarssl_chars_for_cryptogram(cg1); \
      ITEM_CONSTRAINTS_NO_COLLISION_INJEVTIVE_PAYLOAD_SWITCH(CG2) \
  }
          
lemma void item_constraints_no_collision_injective(list<char> cs, item i1, 
                                                                  item i2)
  requires [_]item_constraints_no_collision(i1, cs, ?pub) &*&
           [_]item_constraints_no_collision(i2, cs, pub);
  ensures  collision_in_run() ? true : i1 == i2;
{
  switch (i1)
  {
    case data_item(d1):
      open [_]item_constraints_no_collision(i1, cs, pub);
      open [_]item_constraints_no_collision(i2, cs, pub);
      switch (i2)
      {
        case data_item(d2):
          assert i1 == i2;
        case pair_item(f2, s2): 
          assert false;
        case nonce_item(p2, c2, inc2):
          assert false;
        case hash_item(pay2):
          assert false;
        case symmetric_key_item(p2, c2):
          assert false;
        case public_key_item(p2, c2):
          assert false;
        case private_key_item(p2, c2):
          assert false;
        case hmac_item(p2, c2, pay2):
          assert false;
        case symmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_signature_item(p2, c2, pay2, ent2):
          assert false;
      }
    case pair_item(f1, s1):
      open [_]item_constraints_no_collision(i1, cs, pub);
      open [_]item_constraints_no_collision(i2, cs, pub);
      switch (i2)
      {
        case data_item(d2):
          assert false;
        case pair_item(f2, s2):
          assert [_]item_constraints_no_collision(f1, ?cs_f1, pub);
          assert [_]item_constraints_no_collision(s1, ?cs_s1, pub);
          assert [_]item_constraints_no_collision(f2, ?cs_f2, pub);
          assert [_]item_constraints_no_collision(s2, ?cs_s2, pub);
          int length_f1 = length(cs_f1);
          int length_s1 = length(cs_s1);
          int length_f2 = length(cs_f2);
          int length_s2 = length(cs_s2);
          list<char> length_cs_f1 = chars_of_unbounded_int(length_f1);
          list<char> length_cs_f2 = chars_of_unbounded_int(length_f2);
          
          drop_append(length(length_cs_f1), length_cs_f1, append(cs_f1, cs_s1));
          drop_append(length(length_cs_f2), length_cs_f2, append(cs_f2, cs_s2));
          take_append(length(length_cs_f1), length_cs_f1, append(cs_f1, cs_s1));
          take_append(length(length_cs_f2), length_cs_f2, append(cs_f2, cs_s2));
          drop_append(length_f1, cs_f1, cs_s1);
          drop_append(length_f2, cs_f2, cs_s2);
          take_append(length_f1, cs_f1, cs_s1);
          take_append(length_f2, cs_f2, cs_s2);

          if (length_f1 == length_f2)
          {
            item_constraints_no_collision_injective(cs_f1, f1, f2);
            item_constraints_no_collision_injective(cs_s1, s1, s2);
          }
          else
          {
            chars_of_unbounded_int_bounds(length_f1);
            chars_of_unbounded_int_bounds(length_f2);
            assert length(length_cs_f1) > 0;
            assert length(length_cs_f2) > 0;
            head_append(length_cs_f1, append(cs_f1, cs_s1));
            head_append(length_cs_f2, append(cs_f2, cs_s2));
            assert head(length_cs_f1) == head(length_cs_f1);
            assert length_f1 != length_f2;
            if (length(length_cs_f1) == sizeof(int)) 
            {
              if (length(length_cs_f2) == sizeof(int)) 
              {
                assert chars_of_int(length_f1) == chars_of_int(length_f2);
                chars_of_int_injective(length_f1, length_f2);
              }
            }
          }
          assert collision_in_run() ? true : i1 == i2;
        case nonce_item(p2, c2, inc2):
          assert false;
        case hash_item(pay2):
          assert false;
        case symmetric_key_item(p2, c2):
          assert false;
        case public_key_item(p2, c2):
          assert false;
        case private_key_item(p2, c2):
          assert false;
        case hmac_item(p2, c2, pay2):
          assert false;
        case symmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_signature_item(p2, c2, pay2, ent2):
          assert false;
      }
    case nonce_item(p1, c1, inc1):
      open [_]item_constraints_no_collision(i1, cs, pub);
      open [_]item_constraints_no_collision(i2, cs, pub);
      switch (i2)
      {
        case data_item(d2):
          assert false;
        case pair_item(f2, s2): 
          assert false;
        case nonce_item(p2, c2, inc2):
          polarssl_cryptogram cg1 = polarssl_random(p1, c1);
          polarssl_cryptogram cg2 = polarssl_random(p2, c2);
          polarssl_chars_for_cryptogram_injective(cg1, cg2);
          assert collision_in_run() ? true : i1 == i2;
        case hash_item(pay2):
          assert false;
        case symmetric_key_item(p2, c2):
          assert false;
        case public_key_item(p2, c2):
          assert false;
        case private_key_item(p2, c2):
          assert false;
        case hmac_item(p2, c2, pay2):
          assert false;
        case symmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_signature_item(p2, c2, pay2, ent2):
          assert false;
      }
    case hash_item(pay1):
      open [_]item_constraints_no_collision(i1, cs, pub);
      open [_]item_constraints_no_collision(i2, cs, pub);
      assert cs == cons('d', ?cs_cg);
      switch (i2)
      {
        case data_item(d2):
          assert false;
        case pair_item(f2, s2): 
          assert false;
        case nonce_item(p2, c2, inc2):
          assert false;
        case hash_item(pay2):
          ITEM_CONSTRAINTS_NO_COLLISION_INJEVTIVE_PAYLOAD_DOUBLE_SWITCH(
            polarssl_hash(cs_pay1),
            polarssl_hash(cs_pay2)
          )
        case symmetric_key_item(p2, c2):
          assert false;
        case public_key_item(p2, c2):
          assert false;
        case private_key_item(p2, c2):
          assert false;
        case hmac_item(p2, c2, pay2):
          assert false;
        case symmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_signature_item(p2, c2, pay2, ent2):
          assert false;
      }
    case symmetric_key_item(p1, c1):
      open [_]item_constraints_no_collision(i1, cs, pub);
      open [_]item_constraints_no_collision(i2, cs, pub);
      switch (i2)
      {
        case data_item(d2):
          assert false;
        case pair_item(f2, s2): 
          assert false;
        case nonce_item(p2, c2, inc2):
          assert false;
        case hash_item(pay2):
          assert false;
        case symmetric_key_item(p2, c2):
          polarssl_cryptogram cg1 = polarssl_symmetric_key(p1, c1);
          polarssl_cryptogram cg2 = polarssl_symmetric_key(p2, c2);
          polarssl_chars_for_cryptogram_injective(cg1, cg2);
          assert collision_in_run() ? true : i1 == i2;
        case public_key_item(p2, c2):
          assert false;
        case private_key_item(p2, c2):
          assert false;
        case hmac_item(p2, c2, pay2):
          assert false;
        case symmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_signature_item(p2, c2, pay2, ent2):
          assert false;
      }
    case public_key_item(p1, c1):
      open [_]item_constraints_no_collision(i1, cs, pub);
      open [_]item_constraints_no_collision(i2, cs, pub);
      switch (i2)
      {
        case data_item(d2):
          assert false;
        case pair_item(f2, s2): 
          assert false;
        case nonce_item(p2, c2, inc2):
          assert false;
        case hash_item(pay2):
          assert false;
        case symmetric_key_item(p2, c2):
          assert false;
        case public_key_item(p2, c2):
          polarssl_cryptogram cg1 = polarssl_public_key(p1, c1);
          polarssl_cryptogram cg2 = polarssl_public_key(p2, c2);
          polarssl_chars_for_cryptogram_injective(cg1, cg2);
          assert collision_in_run() ? true : i1 == i2;
        case private_key_item(p2, c2):
          assert false;
        case hmac_item(p2, c2, pay2):
          assert false;
        case symmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_signature_item(p2, c2, pay2, ent2):
          assert false;
      }
    case private_key_item(p1, c1):
      open [_]item_constraints_no_collision(i1, cs, pub);
      open [_]item_constraints_no_collision(i2, cs, pub);
      switch (i2)
      {
        case data_item(d2):
          assert false;
        case pair_item(f2, s2): 
          assert false;
        case nonce_item(p2, c2, inc2):
          assert false;
        case hash_item(pay2):
          assert false;
        case symmetric_key_item(p2, c2):
          assert false;
        case public_key_item(p2, c2):
          assert false;
        case private_key_item(p2, c2):
          polarssl_cryptogram cg1 = polarssl_private_key(p1, c1);
          polarssl_cryptogram cg2 = polarssl_private_key(p2, c2);
          polarssl_chars_for_cryptogram_injective(cg1, cg2);
          assert collision_in_run() ? true : i1 == i2;
        case hmac_item(p2, c2, pay2):
          assert false;
        case symmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_signature_item(p2, c2, pay2, ent2):
          assert false;
      }
    case hmac_item(p1, c1, pay1):
      open [_]item_constraints_no_collision(i1, cs, pub);
      open [_]item_constraints_no_collision(i2, cs, pub);
      switch (i2)
      {
        case data_item(d2):
          assert false;
        case pair_item(f2, s2): 
          assert false;
        case nonce_item(p2, c2, inc2):
          assert false;
        case hash_item(pay2):
          assert false;
        case symmetric_key_item(p2, c2):
          assert false;
        case public_key_item(p2, c2):
          assert false;
        case private_key_item(p2, c2):
          assert false;
        case hmac_item(p2, c2, pay2):
          assert cs == cons('h', ?cs_cg);
          ITEM_CONSTRAINTS_NO_COLLISION_INJEVTIVE_PAYLOAD_DOUBLE_SWITCH(
            polarssl_hmac(p1, c1, cs_pay1),
            polarssl_hmac(p2, c2, cs_pay2)
          )
        case symmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_signature_item(p2, c2, pay2, ent2):
          assert false;
      }
    case symmetric_encrypted_item(p1, c1, pay1, ent1):
      open [_]item_constraints_no_collision(i1, cs, pub);
      open [_]item_constraints_no_collision(i2, cs, pub);
      switch (i2)
      {
        case data_item(d2):
          assert false;
        case pair_item(f2, s2): 
          assert false;
        case nonce_item(p2, c2, inc2):
          assert false;
        case hash_item(pay2):
          assert false;
        case symmetric_key_item(p2, c2):
          assert false;
        case public_key_item(p2, c2):
          assert false;
        case private_key_item(p2, c2):
          assert false;
        case hmac_item(p2, c2, pay2):
          assert false;
        case symmetric_encrypted_item(p2, c2, pay2, ent2):
          assert i1 == symmetric_encrypted_item(p1, c1, pay1, ent1);
          assert i2 == symmetric_encrypted_item(p2, c2, pay2, ent2);
          assert [_]symmetric_encryption_entropy(i1)(?mac1, ?iv1);
          assert [_]symmetric_encryption_entropy(i2)(?mac2, ?iv2);
          list<char> ent1_1 = take(GCM_ENT_SIZE, ent1);
          list<char> ent1_2 = drop(GCM_ENT_SIZE, ent1);
          list<char> cs_mac1 = take(GCM_ENT_SIZE, ent1_1);
          list<char> cs_iv1 = drop(GCM_ENT_SIZE, ent1_1);
          append_take_drop_n(ent1_1, GCM_ENT_SIZE);
          assert ent1_1 == append(cs_mac1, cs_iv1);
          assert ent1_2 == cons(length(mac1), append(mac1, iv1));
          assert ent1 == append(ent1_1, ent1_2);
          list<char> ent2_1 = take(GCM_ENT_SIZE, ent2);
          list<char> ent2_2 = drop(GCM_ENT_SIZE, ent2);
          list<char> cs_mac2 = take(GCM_ENT_SIZE, ent2_1);
          list<char> cs_iv2 = drop(GCM_ENT_SIZE, ent2_1);
          append_take_drop_n(ent2_1, GCM_ENT_SIZE);
          assert ent2_1 == append(cs_mac2, cs_iv2);
          assert ent2_2 == cons(length(mac2), append(mac2, iv2));
          assert ent2 == append(ent2_1, ent2_2);
          
          assert cs == cons('i', ?cs0);
          list<char> cs_cg = drop(GCM_ENT_SIZE, cs0);
          append_take_drop_n(cs0, GCM_ENT_SIZE);
          assert cs0 == append(ent1_1, cs_cg);
          assert cs0 == append(ent2_1, cs_cg);
          
          ITEM_CONSTRAINTS_NO_COLLISION_INJEVTIVE_PAYLOAD_DOUBLE_SWITCH(
            polarssl_auth_encrypted(p1, c1, mac1, cs_pay1, iv1),
            polarssl_auth_encrypted(p2, c2, mac2, cs_pay2, iv2)
          )
        case asymmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_signature_item(p2, c2, pay2, ent2):
          assert false;
      }
    case asymmetric_encrypted_item(p1, c1, pay1, ent1):
      open [_]item_constraints_no_collision(i1, cs, pub);
      open [_]item_constraints_no_collision(i2, cs, pub);
      switch (i2)
      {
        case data_item(d2):
          assert false;
        case pair_item(f2, s2): 
          assert false;
        case nonce_item(p2, c2, inc2):
          assert false;
        case hash_item(pay2):
          assert false;
        case symmetric_key_item(p2, c2):
          assert false;
        case public_key_item(p2, c2):
          assert false;
        case private_key_item(p2, c2):
          assert false;
        case hmac_item(p2, c2, pay2):
          assert false;
        case symmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_encrypted_item(p2, c2, pay2, ent2):
          assert cs == cons('j', ?cs_cg);
          ITEM_CONSTRAINTS_NO_COLLISION_INJEVTIVE_PAYLOAD_DOUBLE_SWITCH(
            polarssl_asym_encrypted(p1, c1, cs_pay1, ent1),
            polarssl_asym_encrypted(p2, c2, cs_pay2, ent2)
          )
        case asymmetric_signature_item(p2, c2, pay2, ent2):
          assert false;
      }
    case asymmetric_signature_item(p1, c1, pay1, ent1):
      open [_]item_constraints_no_collision(i1, cs, pub);
      open [_]item_constraints_no_collision(i2, cs, pub);
      switch (i2)
      {
        case data_item(d2):
          assert false;
        case pair_item(f2, s2): 
          assert false;
        case nonce_item(p2, c2, inc2):
          assert false;
        case hash_item(pay2):
          assert false;
        case symmetric_key_item(p2, c2):
          assert false;
        case public_key_item(p2, c2):
          assert false;
        case private_key_item(p2, c2):
          assert false;
        case hmac_item(p2, c2, pay2):
          assert false;
        case symmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_encrypted_item(p2, c2, pay2, ent2):
          assert false;
        case asymmetric_signature_item(p2, c2, pay2, ent2):
          assert cs == cons('k', ?cs_cg);
          ITEM_CONSTRAINTS_NO_COLLISION_INJEVTIVE_PAYLOAD_DOUBLE_SWITCH(
            polarssl_asym_signature(p1, c1, cs_pay1, ent1),
            polarssl_asym_signature(p2, c2, cs_pay2, ent2)
          )
      }
  }
}

lemma void item_constraints_injective(list<char> cs, item i1, item i2)
  requires [_]item_constraints(?b1, i1, cs, ?pub) &*&
           [_]item_constraints(?b2, i2, cs, pub);
  ensures  collision_in_run() ? true : i1 == i2;
{
  open [_]item_constraints(b1, i1, cs, pub);
  open [_]item_constraints(b2, i2, cs, pub);
    
  if (!b1 && !b2)
    item_constraints_no_collision_injective(cs, i1, i2);
}

lemma void item_constraints_no_collision_bijective(
                                                 list<char> cs1, list<char> cs2,
                                                 item i1, item i2)
  requires true == well_formed_item(i1) &*&
           [_]item_constraints_no_collision(i1, cs1, ?pub) &*&
           [_]item_constraints_no_collision(i2, cs2, pub);
  ensures  collision_in_run() ? true : true == ((cs1 == cs2) == (i1 == i2));
{
  if (cs1 == cs2)
  {
    item_constraints_no_collision_injective(cs1, i1, i2);
  }
  else
  {
    if (i1 == i2)
    {
      item_constraints_no_collision_surjective(cs1, cs2, i1);
    }
  }
}


lemma void item_constraints_bijective(list<char> cs1, list<char> cs2,
                                      item i1, item i2)
  requires true == well_formed_item(i1) &*&
           [_]item_constraints(?b1, i1, cs1, ?pub) &*&
           [_]item_constraints(?b2, i2, cs2, pub);
  ensures  collision_in_run() ? true : true == ((cs1 == cs2) == (i1 == i2));
{
  open [_]item_constraints(b1, i1, cs1, pub);
  open [_]item_constraints(b2, i2, cs2, pub);
    
  if (!b1 && !b2)
    item_constraints_no_collision_bijective(cs1, cs2, i1, i2);
}

@*/

bool item_equals(struct item* item1, struct item* item2)
  /*@ requires [?f1]item(item1, ?i1, ?pub) &*& [?f2]item(item2, ?i2, pub) &*&
               true == well_formed_item(i1); @*/
  /*@ ensures  [f1]item(item1, i1, pub) &*& [f2]item(item2, i2, pub) &*&
               collision_in_run() ? true : result == (i1 == i2); @*/
{
  debug_print("COMPARING ITEMS\n");

  //@ open [f1]item(item1, i1, pub);
  //@ open [f2]item(item2, i2, pub);
  //@ assert [f1]item1->size |-> ?size1;
  //@ assert [f1]item1->content |-> ?cont1 &*& [f1]chars(cont1, size1, ?cs1);
  //@ assert [f2]item2->size |-> ?size2;
  //@ assert [f2]item2->content |-> ?cont2 &*& [f2]chars(cont2, size2, ?cs2);
  //@ open [_]item_constraints(?b1, i1, cs1, pub);
  //@ open [_]item_constraints(?b2, i2, cs2, pub);
  /*@ if (!b1 && !b2) 
        item_constraints_bijective(cs1, cs2, i1, i2); 
      else
        assert true == collision_in_run();
  @*/
  
  if (item1->size == item2->size)
  {
    if (0 == memcmp((void*) (item1->content), (void*) (item2->content),
                                              (unsigned int) item1->size))
    {
      //@ close [f1]item(item1, i1, pub);
      //@ close [f2]item(item2, i2, pub);
      return true;
    }
  }
  //@ close [f1]item(item1, i1, pub);
  //@ close [f2]item(item2, i2, pub);
  return false;
}
