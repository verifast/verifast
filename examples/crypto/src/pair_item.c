#include "pair_item.h"

struct item *create_pair(struct item *first, struct item *second)
  //@ requires item(first, ?fi) &*& item(second, ?si);
  /*@ ensures  item(first, fi) &*& item(second, si) &*&
               item(result, pair_item(fi, si));
  @*/
{
  int* temp1;
  char* temp2;

  //@ open item(first, fi);
  //@ open item(second, si);

  struct item* pair = malloc(sizeof(struct item));
  if (pair == 0){abort_crypto_lib("malloc of item failed");}
  pair->tag = 1;
  if (first->size > INT_MAX - 6 * (int) sizeof(int) - second->size)
    abort_crypto_lib("Pair item to construct is to big");
  pair->size = 4 * (int) sizeof(int) + first->size + second->size;
  pair->content = malloc_wrapper(pair->size);

  //@ assert pair->content |-> ?c_p &*& chars(c_p, ?size_p, ?cs_p);
  
  // First item
  temp1 = (void*) pair->content;
  //@ chars_to_integer(temp1);
  *(temp1) = first->tag;
  //@ integer_to_chars(temp1);
  temp1++;
  //@ chars_to_integer(temp1);
  *(temp1) = first->size;
  //@ integer_to_chars(temp1);
  temp1++;
  temp2 = (void*) temp1;
  write_buffer(&temp2, first->content, first->size);
  
  // Second item
  temp1 = (void*) temp2;
  //@ chars_to_integer(temp1);
  *(temp1) = second->tag;
  //@ integer_to_chars(temp1);
  temp1++;
  //@ chars_to_integer(temp1);
  *(temp1) = second->size;
  //@ integer_to_chars(temp1);
  temp1++;
  temp2 = (void*) temp1;
  write_buffer(&temp2, second->content, second->size);

  //@ chars_join(c_p);
  //@ chars_join(c_p);
  //@ chars_join(c_p);
  //@ chars_join(c_p);
  //@ chars_join(c_p);

  //@ list<char> l1 = chars_of_int(tag_for_item(fi));
  //@ list<char> l2 = chars_of_int(length(chars_for_item(fi)));
  //@ list<char> l3 = chars_for_item(fi);
  //@ list<char> l4 = chars_of_int(tag_for_item(si));
  //@ list<char> l5 = chars_of_int(length(chars_for_item(si)));
  //@ list<char> l6 = chars_for_item(si);

  //@ assert chars(c_p, ?l, ?cs);
  /*@
      if (!collision_in_run)
      {
        assert cs == append(append(append(
                     append(append(l1, l2), l3), l4), l5), l6);
        append_assoc(append(append(append(l1, l2), l3), l4), l5, l6);
        append_assoc(append(append(l1, l2), l3), l4, append(l5, l6));
        append_assoc(append(l1, l2), l3, append(l4, append(l5, l6)));
        append_assoc(l1, l2, append(l3, append(l4, append(l5, l6))));   
      }
  @*/

  //@ close item(first, fi);
  //@ close item(second, si);
  //@ close item(pair, pair_item(fi, si));
  return pair;
}

bool is_pair(struct item *item)
  //@ requires item(item, ?i);
  /*@ ensures  item(item, i) &*&
        switch (i)
        {
          case data_item(d0):     
            return result == false;
          case pair_item(f0, s0):     
            return result == true;
          case nonce_item(p0, c0, inc0, i0):
            return result == false;
          case key_item(p0, c0, k0, i0):
            return result == false;
          case hmac_item(k0, pay0):
            return result == false;
          case encrypted_item(k0, pay0, ent0):
            return result == false;
        };
  @*/
{
  //@ open item(item, i);
  return item->tag == 1;
  //@ close item(item, i);
}

void check_is_pair(struct item *item)
  //@ requires item(item, ?i);
  /*@ ensures  
        switch (i)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return item(item, i);
          case nonce_item(p0, c0, inc0, i0):
            return false;
          case key_item(p0, c0, k0, i0):
            return false;
          case hmac_item(k0, pay0):
            return false;
          case encrypted_item(k0, pay0, ent0):
            return false;
        };
  @*/
{
  if (!is_pair(item))
    abort_crypto_lib("Presented item is not a pair item");
}

void pair_get_components(struct item* pair, 
                         struct item** firstp, struct item** secondp)
  /*@ requires item(pair, ?p) &*&
               pointer(firstp, _) &*& pointer(secondp, _); @*/
  /*@ ensures  item(pair, p) &*&
               pointer(firstp, ?fp) &*& pointer(secondp, ?sp) &*&
        switch (p)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return item(fp, ?f1) &*& item(sp, ?s1) &*& 
                   true == if_no_collision(f0 == f1 && s0 == s1);
          case nonce_item(p0, c0, inc0, i0): 
            return false;
          case key_item(p0, c0, k0, i0):
            return false;
          case hmac_item(k0, pay0):
            return false;
          case encrypted_item(k0, pay0, ent0):
            return false;
        };
  @*/
{
  int* temp;

  check_is_pair(pair);
  //@ open item(pair, pair_item(?f0, ?s0));

  struct item *first  = malloc(sizeof(struct item));
  struct item *second = malloc(sizeof(struct item));
  if (first == 0 || second == 0){abort_crypto_lib("malloc of item failed");}

  //@ assert pair->content |-> ?p_content &*& chars(p_content, ?p_size, ?p_cs);
  //@ close [1/2]hide_chars(p_content, p_size, p_cs);
  //@ list<char> l1 = chars_of_int(tag_for_item(f0));
  //@ list<char> l2 = chars_of_int(length(chars_for_item(f0)));
  //@ list<char> l3 = chars_for_item(f0);
  //@ list<char> l4 = chars_of_int(tag_for_item(s0));
  //@ list<char> l5 = chars_of_int(length(chars_for_item(s0)));
  //@ list<char> l6 = chars_for_item(s0);
  /*@ assert true == if_no_collision(
                    p_cs == append(l1, append(l2, append(l3, 
                            append(l4, append(l5, l6)))))); @*/

  //@ chars_limits(p_content);
  if (pair->size < 2 * (int) sizeof(int))
    abort_crypto_lib("Inconsistent pair item 1");
  temp = (void*) pair->content;

  //First item: tag
  //@ chars_split((void*) temp, sizeof(int));
  //@ chars_to_integer(temp);
  first->tag = *(temp);
  check_valid_item_tag(first->tag);
  //@ integer_to_chars(temp);
  /*@ take_append(sizeof(int), l1, append(l2, append(l3, 
                                   append(l4, append(l5, l6))))); @*/
  //@ assert first->tag |-> ?tag1;
  //@ assert true == if_no_collision(tag1 == tag_for_item(f0));

  //First item: size
  temp++; //@ chars_split((void*) temp, sizeof(int));
  //@ chars_to_integer(temp);
  first->size = *(temp);
  check_valid_item_chars_size(first->size);
  //@ integer_to_chars(temp);
  //@ assert first->size |-> ?size1;
  /*@ if (!collision_in_run())
      {
       drop_append(sizeof(int), l1, append(l2, append(l3, 
                                   append(l4, append(l5, l6)))));
       take_append(sizeof(int), l2, append(l3, append(l4, append(l5, l6))));
       assert size1 == length(chars_for_item(f0));
      }
  @*/
  if (first->size < 0 || first->size > pair->size - 2 * (int) sizeof(int))
    abort_crypto_lib("Inconsistent pair item 2");

  //First item: content
  temp++; //@ chars_split((void*) temp, size1);
  first->content = malloc_wrapper(first->size);
  memcpy(first->content, (void*) temp, (unsigned int) first->size);

  //Second item: tag
  temp = (void*) temp + first->size; 
  if (pair->size - first->size - 2 * (int) sizeof(int) < 2 * (int) sizeof(int))
    abort_crypto_lib("Inconsistent pair item 3");
  //@ chars_to_integer(temp);
  second->tag = *(temp);
  check_valid_item_tag(second->tag);
  //@ integer_to_chars(temp);
  //@ assert second->tag |-> ?tag2;
  /*@ if (!collision_in_run())
      {
        drop_append(sizeof(int), l2, append(l3, append(l4, append(l5, l6))));
        drop_append(size1, l3, append(l4, append(l5, l6)));
        take_append(sizeof(int), l4, append(l5, l6));
        assert tag2 == tag_for_item(s0);
      }
  @*/

  temp++; //@ chars_split((void*) temp, sizeof(int));
  //@ chars_to_integer(temp);
  second->size = *(temp);
  check_valid_item_chars_size(second->size);
  //@ integer_to_chars(temp);
  //@ assert second->size |-> ?size2;
  /*@ if (!collision_in_run())
      {
        drop_append(sizeof(int), l4, append(l5, l6));
        take_append(sizeof(int), l5, l6);
        assert size2 == length(chars_for_item(s0));
      }
  @*/
  if (second->size < 0 || 
      second->size != pair->size - first->size - 4 * (int) sizeof(int))
    abort_crypto_lib("Inconsistent pair item 4");

  temp++;
  second->content = malloc_wrapper(second->size);
  memcpy(second->content, (void*) temp, (unsigned int) second->size);

  //First item: constraints
  //@ assert first->content |-> ?content1 &*& chars(content1, size1, ?f_cs);
  /*@ if (!collision_in_run())
      {
        drop_append(sizeof(int), l1, append(l2, append(l3, 
                                   append(l4, append(l5, l6)))));
        drop_append(sizeof(int), l2, append(l3, append(l4, append(l5, l6))));
        take_append(length(chars_for_item(f0)), l3, append(l4, append(l5, l6)));
        assert l3 == f_cs;
        close item(first, f0);
      }
      else
      {
        dummy_item_for_tag_has_valid_tag(tag1);
        close item(first, dummy_item_for_tag(tag1));
      }
  @*/
  *firstp =  first;
  //Second item: constraints
  //@ assert second->content |-> ?content2 &*& chars(content2, size2, ?s_cs);
  /*@ if (!collision_in_run())
      {
        drop_append(sizeof(int), l4, append(l5, l6));
        drop_append(sizeof(int), l5, l6);
        assert l6 == s_cs;
        close item(second, s0);
      }
      else
      {
        dummy_item_for_tag_has_valid_tag(tag2);
        item dummy = dummy_item_for_tag(tag2);
        close item(second, dummy);
      }
  @*/
  *secondp = second;

  //@ chars_join(p_content);
  //@ chars_join(p_content);
  //@ chars_join(p_content);
  //@ chars_join(p_content);
  //@ open [1/2]hide_chars(p_content, p_size, p_cs);
  //@ close item(pair, pair_item(f0, s0));
}

struct item *pair_get_first(struct item *pair)
  //@ requires item(pair, ?p);
  /*@ ensures  item(pair, p) &*&
        switch (p)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return item(result, ?f1) &*& 
                   true == if_no_collision(f0 == f1);
          case nonce_item(p0, c0, inc0, i0): 
            return false;
          case key_item(p0, c0, k0, i0):
            return false;
          case hmac_item(k0, pay0):
            return false;
          case encrypted_item(k0, pay0, ent0):
            return false;
        };
  @*/
{
  struct item *first;
  struct item *second;
  pair_get_components(pair, &first, &second);
  item_free(second);
  return first;
}

struct item *pair_get_second(struct item *pair)
  //@ requires item(pair, ?p);
  /*@ ensures  item(pair, p) &*&
        switch (p)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return item(result, ?s1) &*& 
                   true == if_no_collision(s0 == s1);
          case nonce_item(p0, c0, inc0, i0):
            return false;
          case key_item(p0, c0, k0, i0):
            return false;
          case hmac_item(k0, pay0):
            return false;
          case encrypted_item(k0, pay0, ent0):
            return false;
        };
  @*/
{
  struct item *first;
  struct item *second;
  pair_get_components(pair, &first, &second);
  item_free(first);
  return second;
}
