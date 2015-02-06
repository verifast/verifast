#include "pair_item.h"

#include "item_constraints.h"
#include "serialization.h"

struct item *create_pair(struct item *first, struct item *second)
  //@ requires item(first, ?f, ?pub) &*& item(second, ?s, pub);
  /*@ ensures  item(first, f, pub) &*& item(second, s, pub) &*&
               item(result, pair_item(f, s), pub); @*/
{
  struct item* pair = malloc(sizeof(struct item));
  if (pair == 0){abort_crypto_lib("malloc of item failed");}
  
  //@ open item(first, f, pub);
  //@ assert first->content |-> ?cont_f &*& first->size |-> ?size_f;
  //@ assert chars(cont_f, size_f, ?cs_f);
  //@ open [_]item_constraints(?b1, f, cs_f, pub);
  //@ open item(second, s, pub);
  //@ assert second->content |-> ?cont_s &*& second->size |-> ?size_s;
  //@ assert chars(cont_s, size_s, ?cs_s);
  //@ open [_]item_constraints(?b2, s, cs_s, pub);
  
  if (INT_MAX - 1 - (int) sizeof(int) - first->size < second->size) 
    abort_crypto_lib("Requested pair item was to big");
  pair->size = 1 + (int) sizeof(int) + first->size + second->size;
  pair->content = malloc_wrapper(pair->size);
  //@ assert pair->content |-> ?cont &*& pair->size |-> ?size;
  *(pair->content) = 'b';
  {
    //@ assert chars(cont, 1, cons('b', nil));
    char* temp = pair->content + 1;
    //@ chars_split(cont + 1, sizeof(int));
    //@ assert integer(&first->size, ?flen);
    //@ integer_to_chars(&first->size);
    write_buffer(&temp, (void*) &(first->size), (int) sizeof(int));
    //@ chars_to_integer(&first->size);
    //@ assert chars(cont + 1, sizeof(int), chars_of_int(flen));
    //@ chars_split(cont + 1 + sizeof(int), first->size);
    write_buffer(&temp, first->content, first->size);
    //@ assert chars(cont + 1 + sizeof(int), size_f, cs_f);
    write_buffer(&temp, second->content, second->size);
    //@ chars_join(cont + 1 + sizeof(int));
    //@ chars_join(cont + 1);
  }
  //@ list<char> size_f_cs = chars_of_int(size_f);
  //@ list<char> cs = cons('b', append(size_f_cs, append(cs_f, cs_s)));
  //@ append_assoc(size_f_cs, cs_f, cs_s);
  //@ assert chars(cont, size, cs);
  
  //@ item p = pair_item(f, s);
  //@ bool col = collision_in_run();
  /*@ if (col)
      {
        well_formed_pair_item(cs, cs_f, cs_s);
        close well_formed_item_chars(p)(cs);
        leak well_formed_item_chars(p)(cs);
        collision_public(pub,cs);
      }
      else
      {
        close item_constraints_no_collision(p, cs, pub);
        leak item_constraints_no_collision(p, cs, pub);
        item_constraints_no_collision_well_formed(p, p);
        open [_]well_formed_item_chars(p)(cs);
      }
  @*/
  //@ close item_constraints(col, p, cs, pub);
  //@ leak item_constraints(col, p, cs, pub);
  //@ close item(pair, p, pub);
  
  //@ close item(first, f, pub);
  //@ close item(second, s, pub);
  return pair;
}

bool is_pair(struct item *item)
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == pair_item(_, _) : true; @*/
{
  //@ open item(item, i, pub);
  //@ open chars(item->content, ?size, ?cs);
  //@ open [_]item_constraints(?b, i, cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(i, cs, pub);
  return *(item->content) == 'b';
  //@ close item(item, i, pub);
}

void check_is_pair(struct item *item)
  //@ requires item(item, ?p, ?pub);
  //@ ensures  item(item, p, pub) &*& p == pair_item(_, _);
{
  if (!is_pair(item))
    abort_crypto_lib("Presented item is not a pair item");
}

void pair_get_components(struct item* pair, 
                         struct item** firstp, struct item** secondp)
  /*@ requires item(pair, ?p, ?pub) &*&
               p == pair_item(?f0, ?s0) &*&
               pointer(firstp, _) &*& pointer(secondp, _); @*/
  /*@ ensures  item(pair, p, pub) &*&
               pointer(firstp, ?fp) &*& pointer(secondp, ?sp) &*&
                item(fp, ?f1, pub) &*& item(sp, ?s1, pub) &*&
               collision_in_run() ? true : f0 == f1 && s0 == s1; @*/
{
  char* temp;
  
  check_is_pair(pair);
  //@ open item(pair, p, pub);
  //@ assert pair->content |-> ?cont &*& pair->size |-> ?size;
  //@ assert chars(cont, size, ?cs);
  //@ chars_limits(cont);
  //@ open [_]item_constraints(?b, p, cs, pub);
  //@ if (!b) open item_constraints_no_collision(p, cs, pub);
  
  struct item *first  = malloc(sizeof(struct item));
  struct item *second = malloc(sizeof(struct item));
  if (first == 0 || second == 0){abort_crypto_lib("malloc of item failed");}

  temp = pair->content;
  //@ chars_split(cont, 1);
  //@ assert chars(temp, 1, ?cs1);
  //@ assert chars(temp + 1, size - 1, ?cs2);
  //@ assert cs == append(cs1, cs2);
  //@ switch(cs1) {case cons(c0, cs0): case nil:}
  //@ assert cs1 == cons('b', nil);
  //@ assert cs2 == tail(cs);
  
  temp = temp + 1;
  if (pair->size <= 1 + (int) sizeof(int))
    abort_crypto_lib("Found corrupted pair item 1");
  
  //@ chars_split(temp, sizeof(int));
  //@ chars_to_integer(temp);
  first->size = *((int*) (void*) temp);
  if (first->size <= 1 ||
      pair->size - 1 - (int) sizeof(int) <= first->size)
    abort_crypto_lib("Found corrupted pair item 2");
  //@ integer_to_chars(temp);
  //@ assert chars(temp, sizeof(int), ?size_f_cs);
  temp = temp + (int) sizeof(int);
  //@ assert chars(temp, size - 1 - sizeof(int), ?cs3);
  //@ assert cs2 == append(size_f_cs, cs3);
  
  //@ chars_split(temp, first->size);
  first->content = malloc_wrapper(first->size);
  memcpy(first->content, temp, (unsigned int) first->size);
  
  temp = temp + first->size;
  second->size = pair->size - 1 - (int) sizeof(int) - first->size;
  if (second->size <= 1)
    abort_crypto_lib("Found corrupted pair item 3");
  second->content = malloc_wrapper(second->size);
  memcpy(second->content, temp, (unsigned int) second->size);
 
  //@ chars_join(cont + 1 + sizeof(int));
  //@ chars_join(cont + 1);
  //@ assert first->content |-> ?cont_f &*& first->size |-> ?size_f;
  //@ assert second->content |-> ?cont_s &*& second->size |-> ?size_s;
  //@ assert chars(cont_f, size_f, ?cs_f);
  //@ assert chars(cont_s, size_s, ?cs_s);
  
  //@ assert size_f == int_of_chars(size_f_cs);
  //@ assert length(cs_f) == size_f;
  //@ assert chars_of_unbounded_int(size_f) == size_f_cs;
  //@ assert cs3 == append(cs_f, cs_s);
  
  /*@ if (!b) 
      {
        assert [_]item_constraints_no_collision(f0, ?cs_f0, pub);
        item_constraints_no_collision_well_formed(f0, f0);
        open [_]well_formed_item_chars(f0)(cs_f0);
        close item_constraints(false, f0, cs_f0, pub);
        leak item_constraints(false, f0, cs_f0, pub);
        
        assert [_]item_constraints_no_collision(s0, ?cs_s0, pub);
        item_constraints_no_collision_well_formed(s0, s0);
        open [_]well_formed_item_chars(s0)(cs_s0);
        close item_constraints(false, s0, cs_s0, pub);
        leak item_constraints(false, s0, cs_s0, pub);
        
        drop_append(sizeof(int), chars_of_int(length(cs_f0)), 
                    append(cs_f0, cs_s0));
        take_append(sizeof(int), chars_of_int(length(cs_f0)), 
                    append(cs_f0, cs_s0));
        drop_append(length(cs_f0), cs_f0, cs_s0);
        take_append(length(cs_f0), cs_f0, cs_s0);
        close item(first, f0, pub);
        close item(second, s0, pub);
      }
      else
      {
        head_append(size_f_cs, cs3);
        head_mem(size_f_cs);
        assert true == mem(head(cs2), size_f_cs);
        chars_of_int_char_in_bounds(head(tail(cs)), size_f);
        assert INT_MIN <= head(tail(cs)) && head(tail(cs)) <= INT_MAX;
        nat n;
        switch(nat_length(cs)) {case succ(n0): n = n0; case zero: assert false;}
        length_equals_nat_length(cs_f);
        well_formed_upper_bound(cs_f, n, nat_length(cs_f));
        assert true == well_formed(cs_f, nat_length(cs_f));
        switch(nat_length(cs_f)) {case succ(n0): case zero: assert false;}
        assert true == valid_tag(head(cs_f));
        length_equals_nat_length(cs_s);
        well_formed_upper_bound(cs_s, n, nat_length(cs_s));
        assert true == well_formed(cs_s, nat_length(cs_s));
        switch(nat_length(cs_s)) {case succ(n0): case zero: assert false;}
        assert true == valid_tag(head(cs_s));
        
        polarssl_generated_public_cryptograms_subset(polarssl_pub(pub), cs);
        polarssl_cryptograms_in_chars_public_upper_bound_split(
                                                      polarssl_pub(pub), cs, 1);
        polarssl_cryptograms_in_chars_public_upper_bound_split(
                                           polarssl_pub(pub), cs2, sizeof(int));
        polarssl_cryptograms_in_chars_public_upper_bound_split(
                                                polarssl_pub(pub), cs3, size_f);
        polarssl_cryptograms_in_chars_upper_bound_from(cs_f, 
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
        polarssl_cryptograms_in_chars_upper_bound_from(cs_s, 
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
        
        item f = dummy_item_for_tag(head(cs_f));
        tag_for_dummy_item(f, head(cs_f));
        item s = dummy_item_for_tag(head(cs_s));
        tag_for_dummy_item(s, head(cs_s));
        close item_constraints(true, f, cs_f, pub);
        leak item_constraints(true, f, cs_f, pub);
        close item(first, f, pub);
        close item_constraints(true, s, cs_s, pub);
        leak item_constraints(true, s, cs_s, pub);
        close item(second, s, pub);
      }
  @*/

  //@ close item(pair, pair_item(f0, s0), pub);
  
  *firstp = first;
  *secondp = second;
}

struct item *pair_get_first(struct item *pair)
  //@ requires item(pair, ?p, ?pub);
  /*@ ensures  item(pair, p, pub) &*& p == pair_item(?f, ?s) &*& 
               item(result, ?f0, pub) &*&
               collision_in_run() ? true : f == f0; @*/
{
  struct item *first;
  struct item *second;
  check_is_pair(pair);
  pair_get_components(pair, &first, &second);
  item_free(second);
  return first;
}

struct item *pair_get_second(struct item *pair)
  //@ requires item(pair, ?p, ?pub);
  /*@ ensures  item(pair, p, pub) &*& p == pair_item(?f, ?s) &*& 
               item(result, ?s0, pub) &*&
               collision_in_run() ? true : s == s0; @*/
{
  struct item *first;
  struct item *second;
  check_is_pair(pair);
  pair_get_components(pair, &first, &second);
  item_free(first);
  return second;
}
