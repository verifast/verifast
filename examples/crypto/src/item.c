// #include "item.h"

#include "principals.h"
#include "hmac_item.h"

void check_valid_item_tag(int tag)
  //@ requires true;
  //@ ensures  tag >= 0 && tag <= 5;
{
  if (tag < 0 || tag > 5)
    abort_crypto_lib("Found illegal tag");
}

void check_valid_item_size(int size)
  //@ requires true;
  //@ ensures  2 * sizeof(int) < size && size < INT_MAX;
{
  if (2 * (int) sizeof(int) >= size || size >= INT_MAX)
    abort_crypto_lib("Found illegal size for item");
}

void check_valid_item_chars_size(int cs_size)
  //@ requires true;
  //@ ensures  0 < cs_size && cs_size < INT_MAX - 2 * sizeof(int);
{
  if (0 >= cs_size || cs_size >= INT_MAX - 2 * (int) sizeof(int))
    abort_crypto_lib("Found illegal size for item");
}

void check_valid_item_sizes(int size, int cs_size)
  //@ requires true;
  /*@ ensures  2 * sizeof(int) < size && size < INT_MAX &*&
               0 < cs_size && cs_size < INT_MAX - 2 * sizeof(int) &*& 
               size == cs_size + 2 * sizeof(int); @*/
{
   check_valid_item_size(size);
   check_valid_item_chars_size(cs_size);
   if (size != cs_size + 2 * (int) sizeof(int))
    abort_crypto_lib("Found illegal sizes for item");
}

/*@

lemma void chars_and_tag_for_item_injective(item i1, item i2)
  requires [?f0]polarssl_world<item>(?pub) &*&
           chars_for_item(i1) == chars_for_item(i2) &*&
           tag_for_item(i1) == tag_for_item(i2) &*&
           item_constraints(i1, tag_for_item(i1), length(chars_for_item(i1)), 
                            chars_for_item(i1)) == true &*&
           item_constraints(i2, tag_for_item(i2), length(chars_for_item(i2)), 
                            chars_for_item(i2)) == true;
  ensures  [f0]polarssl_world<item>(pub) &*&
           collision_in_run() ? true : i1 == i2;
{
  switch (i1)
  {
    case data_item(d1):
      switch (i2)
      {
        case data_item(d2): chars_of_int_injective(d1, d2);
        case pair_item(ff2, s2): assert i1 == i1;
        case nonce_item(p2, c2, inc2, ii2): assert i1 == i1;
        case key_item(p2, c2, k2, ii2): assert i1 == i1;
        case hmac_item(k2, pay2): assert i1 == i1;
        case encrypted_item(k2, pay2, ent2): assert i1 == i1;
      }
    case pair_item(ff1, s1):
      switch (i2)
      {
        case data_item(d2): assert i1 == i1;
        case pair_item(ff2, s2):
          list<char> l1_1 = chars_of_int(tag_for_item(ff1));
          list<char> l1_2 = chars_of_int(length(chars_for_item(ff1)));
          list<char> l1_3 = chars_for_item(ff1);
          list<char> l1_4 = chars_of_int(tag_for_item(s1));
          list<char> l1_5 = chars_of_int(length(chars_for_item(s1)));
          list<char> l1_6 = chars_for_item(s1);

          list<char> l2_1 = chars_of_int(tag_for_item(ff2));
          list<char> l2_2 = chars_of_int(length(chars_for_item(ff2)));
          list<char> l2_3 = chars_for_item(ff2);
          list<char> l2_4 = chars_of_int(tag_for_item(s2));
          list<char> l2_5 = chars_of_int(length(chars_for_item(s2)));
          list<char> l2_6 = chars_for_item(s2);

          equal_append_chars_of_int(tag_for_item(ff1), tag_for_item(ff2),
                 append(l1_2, append(l1_3, append(l1_4, append(l1_5, l1_6)))),
                 append(l2_2, append(l2_3, append(l2_4, append(l2_5, l2_6)))));
          equal_append_chars_of_int(length(chars_for_item(ff1)),
                                    length(chars_for_item(ff2)),
                 append(l1_3, append(l1_4, append(l1_5, l1_6))),
                 append(l2_3, append(l2_4, append(l2_5, l2_6))));

          take_append(length(chars_for_item(ff1)), l1_3,
                 append(l1_4, append(l1_5, l1_6)));
          take_append(length(chars_for_item(ff2)), l2_3,
                 append(l2_4, append(l2_5, l2_6)));
          drop_append(length(chars_for_item(ff1)), l1_3,
                 append(l1_4, append(l1_5, l1_6)));
          drop_append(length(chars_for_item(ff2)), l2_3,
                 append(l2_4, append(l2_5, l2_6)));

          equal_append_chars_of_int(tag_for_item(s1), tag_for_item(s2),
                 append(l1_5, l1_6), append(l2_5, l2_6));
          equal_append_chars_of_int(length(chars_for_item(s1)),
                                    length(chars_for_item(s2)), l1_6, l2_6);

          chars_and_tag_for_item_injective(ff1, ff2);
          chars_and_tag_for_item_injective(s1, s2); 
        case nonce_item(p2, c2, inc2, ii2): assert i1 == i1;
        case key_item(p2, c2, k2, ii2): assert i1 == i1;
        case hmac_item(k2, pay2): assert i1 == i1;
        case encrypted_item(k2, pay2, ent2): assert i1 == i1;
      }
    case nonce_item(p1, c1, inc1, ii1):
      switch (i2)
      {
        case data_item(d2): assert i1 == i1;
        case pair_item(ff2, s2): assert i1 == i1;
        case nonce_item(p2, c2, inc2, ii2):
          polarssl_item pi1 = polarssl_havege_item(p1, c1);
          polarssl_item pi2 = polarssl_havege_item(p2, c2);
          havege_chars_for_polarssl_item_injective(pi1, pi2);
          drop_append(sizeof(int),
                      chars_of_int(inc1),
                      havege_chars_for_polarssl_item(pi1));
          drop_append(sizeof(int),
                      chars_of_int(inc2),
                      havege_chars_for_polarssl_item(pi2));
          equal_append_chars_of_int(inc1, inc2,
                                    havege_chars_for_polarssl_item(pi1),
                                    havege_chars_for_polarssl_item(pi2));
        case key_item(p2, c2, k2, ii2): assert i1 == i1;
        case hmac_item(k2, pay2): assert i1 == i1;
        case encrypted_item(k2, pay2, ent2): assert i1 == i1;
      }
    case key_item(p1, c1, k1, ii1): assert i1 == i1;
      switch (i2)
      {
        case data_item(d2): i1 == i1;
        case pair_item(ff2, s2): assert i1 == i1;
        case nonce_item(p2, c2, inc2, ii2): assert i1 == i1;
        case key_item(p2, c2, k2, ii2): i1 ==  i1;
          switch (k1)
          {
            case symmetric_key: assert i1 == i1;
              switch (k2)
              {
                case symmetric_key: assert i1 == i1;
                  polarssl_item pi1 = polarssl_havege_item(p1, c1);
                  polarssl_item pi2 = polarssl_havege_item(p2, c2);
                  havege_chars_for_polarssl_item_injective(pi1, pi2);
                case public_key: assert i1 == i1;
                  assert false;
                case private_key: assert i1 == i1;
                  assert false;
              }
            case public_key: assert i1 == i1;
              switch (k2)
              {
                case symmetric_key: assert i1 == i1;
                  assert false;
                case public_key: assert i1 == i1;
                  polarssl_item pi1 = polarssl_rsa_public_key_item(p1, c1);
                  polarssl_item pi2 = polarssl_rsa_public_key_item(p2, c2);
                  rsa_public_key_chars_for_polarssl_item_injective(pi1, pi2);
                case private_key: assert i1 == i1;
                  assert false;
              }
            case private_key: assert i1 == i1;
              switch (k2)
              {
                case symmetric_key: assert i1 == i1;
                  assert false;
                case public_key: assert i1 == i1;
                  assert false;
                case private_key: assert i1 == i1;
                  polarssl_item pi1 = polarssl_rsa_private_key_item(p1, c1);
                  polarssl_item pi2 = polarssl_rsa_private_key_item(p2, c2);
                  rsa_private_key_chars_for_polarssl_item_injective(pi1, pi2);
              }
          }
        case hmac_item(k2, pay2): assert i1 == i1;
        case encrypted_item(k2, pay2, ent2): assert i1 == i1;
      }
    case hmac_item(k1, pay1): assert i1 == i1;
      switch (i2)
      {
        case data_item(d2): i1 == i1;
        case pair_item(ff2, s2): assert i1 == i1;
        case nonce_item(p2, c2, inc2, ii2): assert i1 == i1;
        case key_item(p2, c2, k2, ii2): assert i1 == i1;
        case hmac_item(k2, pay2): assert i1 == i1;
          list<char> k_cs1   = chars_for_item(k1);
          list<char> sk_cs1  = append(chars_of_int(length(chars_for_item(k1))),
                                      k_cs1);
          list<char> tsk_cs1 = append(chars_of_int(tag_for_item(k1)), sk_cs1);

          list<char> p_cs1   = chars_for_item(pay1);
          list<char> sp_cs1  = append(chars_of_int(length(chars_for_item(pay1))),
                                      p_cs1);
          list<char> tsp_cs1 = append(chars_of_int(tag_for_item(pay1)), sp_cs1);

          list<char> k_cs2   = chars_for_item(k2);
          list<char> sk_cs2  = append(chars_of_int(length(chars_for_item(k2))),
                                      k_cs2);
          list<char> tsk_cs2 = append(chars_of_int(tag_for_item(k2)), sk_cs2);

          list<char> p_cs2   = chars_for_item(pay2);
          list<char> sp_cs2  = append(chars_of_int(length(chars_for_item(pay2))),
                                      p_cs2);
          list<char> tsp_cs2 = append(chars_of_int(tag_for_item(pay2)), sp_cs2);

          polarssl_item pi1 = polarssl_sha512_item(tsk_cs1, tsp_cs1);
          polarssl_item pi2 = polarssl_sha512_item(tsk_cs2, tsp_cs2);
          sha512_chars_for_polarssl_item_injective(pi1, pi2);
          if (!collision_in_run())
          {
             assert pi1 == pi2;
             assert tsk_cs1 == tsk_cs2;
             assert tsp_cs1 == tsp_cs2;

             equal_append_chars_of_int(tag_for_item(k1), tag_for_item(k2),
                                       sk_cs1, sk_cs2);
             equal_append_chars_of_int(length(chars_for_item(k1)), 
                                       length(chars_for_item(k2)),
                                       k_cs1, k_cs2);
             equal_append_chars_of_int(tag_for_item(pay1), tag_for_item(pay2),
                                       sp_cs1, sp_cs2);
             equal_append_chars_of_int(length(chars_for_item(pay1)), 
                                       length(chars_for_item(pay2)),
                                       p_cs1, p_cs2);
             chars_and_tag_for_item_injective(k1, k2);
             chars_and_tag_for_item_injective(pay1, pay2);
          }
        case encrypted_item(k2, pay2, ent2): assert i1 == i1;
      }
    case encrypted_item(k1, pay1, ent1):
      switch (i2)
      {
        case data_item(d2): i1 == i1;
        case pair_item(ff2, s2): assert i1 == i1;
        case nonce_item(p2, c2, inc2, ii2): assert i1 == i1;
        case key_item(p2, c2, k2, ii2): assert i1 == i1;
        case hmac_item(k2, pay2): assert i1 == i1;
        case encrypted_item(k2, pay2, ent2): assert i1 == i1;
          switch(k1)
          {
            case data_item(d3): i1 == i1;
              assert false;
            case pair_item(ff3, s3):
              assert false;
            case nonce_item(p3, c3, inc3, ii3):
              assert false;
            case hmac_item(k3, pay3):
              assert false;
            case encrypted_item(k3, pay3, ent3):
              assert false;
            case key_item(p3, c3, kind3, ii3):
              switch(k2)
              {
                case data_item(d4): i1 == i1;
                  assert false;
                case pair_item(ff4, s4):
                  assert false;
                case nonce_item(p4, c4, inc4, ii4):
                  assert false;
                case hmac_item(k4, pay4):
                  assert false;
                case encrypted_item(k4, pay4, ent4):
                  assert false;
                case key_item(p4, c4, kind4, ii4):
                  list<char> p_cs11 = chars_for_item(pay1);
                  list<char> p_cs12 = append(chars_of_int(length(chars_for_item(pay1))),
                                              p_cs11);
                  list<char> p_cs1  = append(chars_of_int(tag_for_item(pay1)), p_cs12);
                  list<char> p_cs21 = chars_for_item(pay2);
                  list<char> p_cs22 = append(chars_of_int(length(chars_for_item(pay2))),
                                             p_cs21);
                  list<char> p_cs2  = append(chars_of_int(tag_for_item(pay2)), p_cs22);
                  switch(kind3)
                  {
                    case symmetric_key:
                      switch(kind4)
                      {
                        case symmetric_key:
                          //i1
                          int ent_index1     = int_of_chars(take(sizeof(int), ent1));
                          list<char> ent_iv1 = drop(sizeof(int), ent1);
                                  
                          list<char> k_cs11 = chars_for_item(k1);
                          list<char> k_cs12 = append(chars_of_int(length(chars_for_item(k1))),
                                                    k_cs11);
                          list<char> k_cs1  = append(chars_of_int(tag_for_item(k1)), k_cs12);

                          //i2
                          int ent_index2     = int_of_chars(take(sizeof(int), ent2));
                          list<char> ent_iv2 = drop(sizeof(int), ent2);

                          list<char> k_cs21 = chars_for_item(k2);
                          list<char> k_cs22 = append(chars_of_int(length(chars_for_item(k2))),
                                                    k_cs21);
                          list<char> k_cs2  = append(chars_of_int(tag_for_item(k2)), k_cs22);

                          polarssl_item pi1 = polarssl_aes_encrypted_item(k_cs1, ent_index1, ent_iv1, p_cs1);
                          polarssl_item pi2 = polarssl_aes_encrypted_item(k_cs2, ent_index2, ent_iv2, p_cs2);

                          take_append(sizeof(int) + AES_IV_SIZE, ent1, aes_chars_for_polarssl_item(pi1));
                          take_append(sizeof(int) + AES_IV_SIZE, ent2, aes_chars_for_polarssl_item(pi2));
                          drop_append(sizeof(int) + AES_IV_SIZE, ent1, aes_chars_for_polarssl_item(pi1));
                          drop_append(sizeof(int) + AES_IV_SIZE, ent2, aes_chars_for_polarssl_item(pi2));
                          aes_chars_for_polarssl_item_injective(pi1, pi2);
                          if (!collision_in_run())
                          {
                            assert pi1 == pi2;
                            assert k_cs1 == k_cs2;
                            assert p_cs1 == p_cs2;

                            equal_append_chars_of_int(tag_for_item(pay1), tag_for_item(pay2),
                                                      p_cs12, p_cs22);
                            equal_append_chars_of_int(length(chars_for_item(pay1)), 
                                                      length(chars_for_item(pay2)),
                                                      p_cs11, p_cs21);
                            equal_append_chars_of_int(tag_for_item(k1), tag_for_item(k2),
                                                      k_cs12, k_cs22);
                            equal_append_chars_of_int(length(chars_for_item(k1)), 
                                                      length(chars_for_item(k2)),
                                                      k_cs11, k_cs21);
                                                      
                            chars_and_tag_for_item_injective(k1, k2);
                            chars_and_tag_for_item_injective(pay1, pay2);
                          };
                        case public_key:
                          assert false;
                        case private_key:
                          assert false;
                      }
                    case public_key:
                      switch(kind4)
                      {
                        case symmetric_key:
                          assert false;
                        case public_key:
                          polarssl_item pi1 = polarssl_rsa_encrypted_item(p3, c3, p_cs1, ent1);
                          polarssl_item pi2 = polarssl_rsa_encrypted_item(p4, c4, p_cs2, ent2);
                          rsa_encrypted_chars_for_polarssl_item_injective(pi1, pi2);
                          if (!collision_in_run())
                          {
                            equal_append_chars_of_int(tag_for_item(pay1), tag_for_item(pay2),
                                                      p_cs12, p_cs22);
                            equal_append_chars_of_int(length(chars_for_item(pay1)), 
                                                      length(chars_for_item(pay2)),
                                                      p_cs11, p_cs21);
                            chars_and_tag_for_item_injective(pay1, pay2);
                          }
                        case private_key:
                          assert false;
                      }
                    case private_key:
                      assert false;
                  }
              }
          }
      }
  }
}

lemma void chars_for_item_precise(struct item* item1, item i1,
                                  struct item* item2, item i2)
  requires [?f0]polarssl_world<item>(?pub) &*&
           [?f2]item(item1, i1) &*& [?f3]item(item2, i2) &*&
           item1 == item2;
  ensures  [f0]polarssl_world<item>(pub) &*&
           [f2]item(item1, i1) &*& [f3]item(item2, i2) &*&
           collision_in_run() ? true : i1 == i2;
{
  open [f2]item(item1, i1);
  open [f3]item(item2, i2);
  assert [f2]item1->tag |-> ?tag1 &*& [f3]item1->size |-> ?size1;
  assert [f2]item1->content |-> ?cont1 &*& [f3]chars(cont1, size1, ?cs1);
  assert [f3]item2->tag |-> ?tag2 &*& [f3]item2->size |-> ?size2;
  assert [f3]item2->content |-> ?cont2 &*& [f3]chars(cont2, size2, ?cs2);
  close [f2]item(item1, i1);
  close [f3]item(item2, i2);
  if (!collision_in_run())
  {
    chars_and_tag_for_item_injective(i1, i2);
  }
}

lemma void extended_chars_for_item_injective(item i1, item i2)
  requires [?f0]polarssl_world<item>(?pub) &*&
           extended_chars_for_item(i1) == extended_chars_for_item(i2) &*&
           item_constraints(i1, tag_for_item(i1), length(chars_for_item(i1)),
                            chars_for_item(i1)) == true &*&
           item_constraints(i2, tag_for_item(i2), length(chars_for_item(i2)),
                            chars_for_item(i2)) == true;
  ensures  [f0]polarssl_world<item>(pub) &*&
           true == if_no_collision(i1 == i2);
{
  assert extended_chars_for_item(i1) == 
    append(chars_of_int(tag_for_item(i1)),
           append(chars_of_int(length(chars_for_item(i1))),
                  chars_for_item(i1)));
  assert extended_chars_for_item(i1) == 
    append(chars_of_int(tag_for_item(i1)),
           append(chars_of_int(length(chars_for_item(i1))),
                  chars_for_item(i1)));
  take_append(sizeof(int), chars_of_int(tag_for_item(i1)), 
                           append(chars_of_int(length(chars_for_item(i1))),
                           chars_for_item(i1)));
  take_append(sizeof(int), chars_of_int(tag_for_item(i2)), 
                           append(chars_of_int(length(chars_for_item(i2))),
                           chars_for_item(i2)));
  assert chars_of_int(tag_for_item(i1)) == chars_of_int(tag_for_item(i2));
  assert tag_for_item(i1) == tag_for_item(i2);
  
  drop_append(sizeof(int), chars_of_int(tag_for_item(i1)), 
                           append(chars_of_int(length(chars_for_item(i1))),
                           chars_for_item(i1)));
  drop_append(sizeof(int), chars_of_int(tag_for_item(i2)), 
                           append(chars_of_int(length(chars_for_item(i2))),
                           chars_for_item(i2)));
  take_append(sizeof(int), chars_of_int(length(chars_for_item(i1))),
                           chars_for_item(i1));
  take_append(sizeof(int), chars_of_int(length(chars_for_item(i2))),
                           chars_for_item(i2));

  assert chars_of_int(length(chars_for_item(i1))) ==
         chars_of_int(length(chars_for_item(i2)));
  assert length(chars_for_item(i1)) == length(chars_for_item(i2));
  
  drop_append(sizeof(int), chars_of_int(length(chars_for_item(i1))),
                           chars_for_item(i1));
  drop_append(sizeof(int), chars_of_int(length(chars_for_item(i2))),
                           chars_for_item(i2));
  
  assert chars_for_item(i1) == chars_for_item(i2);
  chars_and_tag_for_item_injective(i1 ,i2);
}

@*/

void item_free(struct item* item)
  //@ requires item(item, _);
  //@ ensures  true;
{
  //@ open item(item, _);
  free(item->content);
  free(item);
}

struct item* item_clone(struct item* item)
  //@ requires [?f]item(item, ?i);
  /*@ ensures  [f]item(item, i) &*& 
               item(result, i) &*& result != 0; @*/
{
  //@ open item(item, i);
  struct item* clone = malloc(sizeof(struct item));
  if (clone == 0){abort_crypto_lib("malloc of item failed");}
  clone->tag = item->tag;
  clone->size = item->size;
  clone->content = malloc_wrapper(clone->size);
  memcpy(clone->content, item->content, (unsigned int) clone->size);

  return clone;
  //@ close [f]item(item, i);
  //@ close item(clone, i);
}

bool item_equals(struct item *item1, struct item *item2)
  /*@ requires [?f0]world(?pub) &*&
               [?f2]item(item1, ?i1) &*& [?f3]item(item2, ?i2); @*/
  /*@ ensures  [f0]world(pub) &*&
               [f2]item(item1, i1) &*& [f3]item(item2, i2) &*& 
               collision_in_run() ? true : result == (i1 == i2);
  @*/
{
  debug_print("COMPARING ITEMS\n");

  //@ open [f2]item(item1, i1);
  //@ open [f3]item(item2, i2);
  //@ assert [f2]item1->tag |-> ?tag1 &*& [f2]item1->size |-> ?size1;
  //@ assert [f2]item1->content |-> ?cont1 &*& [f2]chars(cont1, size1, ?cs1);
  //@ assert [f3]item2->tag |-> ?tag2 &*& [f3]item2->size |-> ?size2;
  //@ assert [f3]item2->content |-> ?cont2 &*& [f3]chars(cont2, size2, ?cs2);

  if (item1 != item2)
  {
    if (item1->tag == item2->tag && item1->size == item2->size)
    {
      if (0 == memcmp((void*) (item1->content), (void*) (item2->content),
                                                (unsigned int) item1->size))
      {
#ifdef DEBUG
        debug_print("\tFound different, but identical items");
#endif
        //@ close [f2]item(item1, i1);
        //@ close [f3]item(item2, i2);
        /*@ 
            if (!collision_in_run())
            {
              open  [f0]world(pub);
              chars_and_tag_for_item_injective(i1, i2);
              close [f0]world(pub);
            }
        @*/
        return true;
      }
    }

    //@ close [f2]item(item1, i1);
    //@ close [f3]item(item2, i2);
    return false;
  }
  else
  {
    //@ open  [f0]world(pub);
    //@ close [f2]item(item1, i1);
    //@ close [f3]item(item2, i2);
    //@ chars_for_item_precise(item1, i1, item2, i2);
    //@ close [f0]world(pub);
    return true;
  }
}

