#include "pair_item.h"

#include "item_constraints.h"
#include "serialization.h"

bool is_pair(struct item *item)
  //@ requires [?f]world(?pub) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub) &*& item(item, i, pub) &*&
               result ? i == pair_item(_, _) : true; @*/
{
  //@ open [f]world(pub);
  //@ open item(item, i, pub);
  //@ open [_]item_constraints(i, ?cs, pub);
  return item_tag(item->content, item->size) == 'b';
  //@ close item(item, i, pub);
  //@ close [f]world(pub);
}

void check_is_pair(struct item *item)
  //@ requires [?f]world(?pub) &*& item(item, ?p, pub);
  /*@ ensures  [f]world(pub) &*& item(item, p, pub) &*&
               p == pair_item(_, _); @*/
{
  if (!is_pair(item))
    abort_crypto_lib("Presented item is not a pair item");
}

struct item *create_pair(struct item *first, struct item *second)
  /*@ requires [?f0]world(?pub) &*&
               item(first, ?f, pub) &*& item(second, ?s, pub); @*/
  /*@ ensures  [f0]world(pub) &*&
               item(first, f, pub) &*& item(second, s, pub) &*&
               item(result, pair_item(f, s), pub); @*/
{
  //@ open [f0]world(pub);
  struct item* pair = malloc(sizeof(struct item));
  if (pair == 0){abort_crypto_lib("malloc of item failed");}

  //@ open item(first, f, pub);
  //@ assert first->content |-> ?cont_f &*& first->size |-> ?size_f;
  //@ assert crypto_chars(secret, cont_f, size_f, ?cs_f);
  //@ assert [_]item_constraints(f, cs_f, pub);
  //@ well_formed_item_constraints(f, f);
  //@ open [_]well_formed_item_chars(f)(cs_f);
  //@ open item(second, s, pub);
  //@ assert second->content |-> ?cont_s &*& second->size |-> ?size_s;
  //@ assert crypto_chars(secret, cont_s, size_s, ?cs_s);
  //@ well_formed_item_constraints(s, s);
  //@ open [_]well_formed_item_chars(s)(cs_s);
  //@ assert [_]item_constraints(s, cs_s, pub);
  if (INT_MAX - TAG_LENGTH - (int) sizeof(int) - first->size < second->size)
    abort_crypto_lib("Requested pair item was to big");
  pair->size = TAG_LENGTH + (int) sizeof(int) + first->size + second->size;
  pair->content = malloc_wrapper(pair->size);
  //@ assert pair->content |-> ?cont &*& pair->size |-> ?size;
  write_tag(pair->content, TAG_PAIR);
  {
    //@ assert chars(cont, TAG_LENGTH, full_tag(TAG_PAIR));
    //@ public_chars(cont, TAG_LENGTH);
    //@ chars_to_secret_crypto_chars(cont, TAG_LENGTH);
    char* temp = pair->content + TAG_LENGTH;
    //@ chars_split(cont + TAG_LENGTH, sizeof(int));
    //@ assert integer(&first->size, ?flen);
    //@ integer_to_chars(&first->size);
    //@ open chars((void*) &first->size, sizeof(int), chars_of_int(flen));
    //@ character_limits((void*) &first->size);
    //@ close chars((void*) &first->size, sizeof(int), chars_of_int(flen));
    //@ public_chars((void*) &first->size, sizeof(int));
    //@ public_chars((void*) &first->size, sizeof(int));
    //@ chars_to_crypto_chars((void*) &first->size, sizeof(int));
    write_buffer(&temp, (void*) &(first->size), (int) sizeof(int));
    //@ crypto_chars_to_chars((void*) &first->size, sizeof(int));
    //@ chars_to_secret_crypto_chars(temp - sizeof(int), sizeof(int));
    //@ chars_to_integer(&first->size);
    //@ chars_split(cont + TAG_LENGTH + sizeof(int), first->size);
    write_buffer(&temp, first->content, first->size);
    write_buffer(&temp, second->content, second->size);
    //@ crypto_chars_join(cont + TAG_LENGTH + sizeof(int));
    //@ crypto_chars_join(cont + TAG_LENGTH);
    //@ crypto_chars_join(cont);
  }
  //@ list<char> size_f_cs = chars_of_int(size_f);
  //@ list<char> cs0 = append(size_f_cs, append(cs_f, cs_s));
  //@ list<char> cs = append(full_tag(TAG_PAIR), cs0);
  //@ take_append(TAG_LENGTH, full_tag(TAG_PAIR), cs0);
  //@ drop_append(TAG_LENGTH, full_tag(TAG_PAIR), cs0);
  //@ assert length(size_f_cs) == sizeof(int);
  //@ take_append(sizeof(int), size_f_cs, append(cs_f, cs_s));
  //@ drop_append(sizeof(int), size_f_cs, append(cs_f, cs_s));
  //@ take_append(size_f, cs_f, cs_s);
  //@ drop_append(size_f, cs_f, cs_s);
  //@ assert drop(sizeof(int), cs0) == append(cs_f, cs_s);
  //@ assert size_f_cs == chars_of_unbounded_int(length(cs_f));
  //@ append_assoc(size_f_cs, cs_f, cs_s);
  //@ assert crypto_chars(secret, cont, size, cs);
  //@ item p = pair_item(f, s);
  //@ close ic_pair(p)(cs_f, cs_s);
  //@ length_equals_nat_length(cs);
  //@ length_equals_nat_length(cs0);
  //@ drop_drop(sizeof(int), TAG_LENGTH, cs);
  //@ head_append(full_tag(TAG_PAIR), cs0);
  /*@ switch(nat_length(cs))
      {
        case succ(n):
          well_formed_upper_bound(cs_f, nat_length(cs_f), n);
          well_formed_upper_bound(cs_s, nat_length(cs_s), n);
        case zero:
          assert false;
      }
  @*/
  /*@ if(col)
      {
        public_chars(cont, size);
        public_generated_split(polarssl_pub(pub), cs, TAG_LENGTH);
      }
  @*/
  //@ close ic_parts(p)(full_tag(TAG_PAIR), cs0);
  //@ close item_constraints(p, cs, pub);
  //@ leak item_constraints(p, cs, pub);
  //@ close item(pair, p, pub);

  //@ close item(first, f, pub);
  //@ close item(second, s, pub);
  return pair;
  //@ close [f0]world(pub);
}

void pair_get_components(struct item* pair,
                         struct item** firstp, struct item** secondp)
  /*@ requires [?f]world(?pub) &*& item(pair, ?p, pub) &*&
               p == pair_item(?f0, ?s0) &*&
               pointer(firstp, _) &*& pointer(secondp, _); @*/
  /*@ ensures  [f]world(pub) &*& item(pair, p, pub) &*&
               pointer(firstp, ?fp) &*& pointer(secondp, ?sp) &*&
                item(fp, ?f1, pub) &*& item(sp, ?s1, pub) &*&
               col ? true : f0 == f1 && s0 == s1; @*/
{
  char* temp;

  check_is_pair(pair);
  //@ open item(pair, p, pub);
  //@ assert pair->content |-> ?cont &*& pair->size |-> ?size;
  //@ assert crypto_chars(secret, cont, size, ?cs);
  //@ open [_]item_constraints(p, cs, pub);
  //@ assert [_]ic_parts(p)(?cs_tag, ?cs_cont);
  //@ take_append(TAG_LENGTH, cs_tag, cs_cont);
  //@ drop_append(TAG_LENGTH, cs_tag, cs_cont);
  //@ assert [_]ic_pair(p)(?cs_f, ?cs_s);
  
  struct item *first  = malloc(sizeof(struct item));
  struct item *second = malloc(sizeof(struct item));
  if (first == 0 || second == 0){abort_crypto_lib("malloc of item failed");}

  temp = pair->content;
  //@ crypto_chars_split(cont, TAG_LENGTH);
  //@ if (col) public_generated_split(polarssl_pub(pub), cs, TAG_LENGTH);
  //@ assert crypto_chars(secret, temp, TAG_LENGTH, cs_tag);
  //@ assert crypto_chars(secret, temp + TAG_LENGTH, size - TAG_LENGTH, cs_cont);
  //@ assert cs_tag == full_tag(TAG_PAIR);
  //@ assert cs == append(cs_tag, cs_cont);
  //@ switch(cs_tag) {case cons(c0, cs0): case nil: assert false;}
  //@ assert cs_tag == cons(TAG_PAIR, _);
  

  temp = temp + TAG_LENGTH;
  if (pair->size <= TAG_LENGTH + (int) sizeof(int))
    abort_crypto_lib("Found corrupted pair item 1");

  //@ open [f]world(pub);
  //@ crypto_chars_split(temp, sizeof(int));
  //@ if (col) public_generated_split(polarssl_pub(pub), cs_cont, sizeof(int));
  //@ assert crypto_chars(secret, temp, sizeof(int), ?cs_size_f);
  //@ assert crypto_chars(secret, temp + sizeof(int), size - TAG_LENGTH - sizeof(int), ?cs_p);
  //@ take_append(sizeof(int), cs_size_f, cs_p);
  //@ drop_append(sizeof(int), cs_size_f, cs_p);
  //@ public_crypto_chars(temp, sizeof(int));
  //@ chars_to_integer(temp);
  first->size = *((int*) (void*) temp);
  second->size = pair->size - TAG_LENGTH - (int) sizeof(int) - first->size;
  //@ assert first->size |-> ?size_f &*& second->size |-> ?size_s;
  if (first->size <= TAG_LENGTH ||
      pair->size - TAG_LENGTH - (int) sizeof(int) <= first->size)
    abort_crypto_lib("Found corrupted pair item 2");
  //@ integer_to_chars(temp);
  temp = temp + (int) sizeof(int);
  //@ assert cs_cont == append(cs_size_f, cs_p);
  //@ append_assoc(cs_cont, cs_size_f, cs_p);
  //@ crypto_chars_split(temp, first->size);
  //@ if (col) public_generated_split(polarssl_pub(pub), cs_p, first->size);
  //@ take_append(size_f, cs_f, cs_s);
  //@ drop_append(size_f, cs_f, cs_s);
  //@ assert crypto_chars(secret, temp, size_f, cs_f);
  //@ assert crypto_chars(secret, temp + size_f, size_s, cs_s);
  //@ assert cs_p == append(cs_f, cs_s);
  first->content = malloc_wrapper(first->size);
  if (first->size <= MINIMAL_STRING_SIZE)
    abort_crypto_lib("Found corrupted pair item 3");
  memcpy(first->content, temp, (unsigned int) first->size);
  temp = temp + first->size;
  if (second->size <= MINIMAL_STRING_SIZE)
    abort_crypto_lib("Found corrupted pair item 4");
  second->content = malloc_wrapper(second->size);
  memcpy(second->content, temp, (unsigned int) second->size);
  //@ crypto_chars_join(cont + TAG_LENGTH + sizeof(int));
  //@ chars_to_secret_crypto_chars(cont + TAG_LENGTH, sizeof(int));
  //@ crypto_chars_join(cont + TAG_LENGTH);
  //@ assert first->content |-> ?cont_f &*& second->content |-> ?cont_s;
  //@ assert crypto_chars(secret, cont_f, size_f, cs_f);
  //@ assert crypto_chars(secret, cont_s, size_s, cs_s);
  //@ assert size_f == int_of_chars(cs_size_f);
  //@ assert chars_of_unbounded_int(size_f) == cs_size_f;
  //@ assert length(cs_f) == size_f;
  //@ assert [_]item_constraints(f0, ?cs_f0, pub);
  //@ assert [_]item_constraints(s0, ?cs_s0, pub);
  /*@ drop_append(sizeof(int), chars_of_int(length(cs_f0)),
                  append(cs_f0, cs_s0)); @*/
  /*@ take_append(sizeof(int), chars_of_int(length(cs_f0)),
                  append(cs_f0, cs_s0)); @*/
  //@ drop_append(length(cs_f0), cs_f0, cs_s0);
  //@ take_append(length(cs_f0), cs_f0, cs_s0);
  //@ close item(first, f0, pub);
  //@ close item(second, s0, pub);
  //@ close item(pair, pair_item(f0, s0), pub);

  *firstp = first;
  *secondp = second;
  //@ close [f]world(pub);
}

struct item *pair_get_first(struct item *pair)
  //@ requires [?f0]world(?pub) &*& item(pair, ?p, pub);
  /*@ ensures  [f0]world(pub) &*& item(pair, p, pub) &*&
               p == pair_item(?fst, ?snd) &*&
               item(result, ?fst0, pub) &*&
               col ? true : fst == fst0; @*/
{
  struct item *first;
  struct item *second;
  check_is_pair(pair);
  pair_get_components(pair, &first, &second);
  item_free(second);
  return first;
}

struct item *pair_get_second(struct item *pair)
  //@ requires [?f0]world(?pub) &*& item(pair, ?p, pub);
  /*@ ensures  [f0]world(pub) &*&item(pair, p, pub) &*&
               p == pair_item(?fst, ?snd) &*&
               item(result, ?snd0, pub) &*&
               col ? true : snd == snd0; @*/
{
  struct item *first;
  struct item *second;
  check_is_pair(pair);
  pair_get_components(pair, &first, &second);
  item_free(first);
  return second;
}
