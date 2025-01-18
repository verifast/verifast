#include "pair_item.h"

#include "item_constraints.h"
#include "serialization.h"

bool is_pair(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == pair_item(_, _) : true; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open item(item, i, pub);
  //@ open [_]item_constraints(i, ?cs, pub);
  return item_tag(item->content, item->size) == 'b';
  //@ close item(item, i, pub);
  //@ close [f]world(pub, key_clsfy);
}

void check_is_pair(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?p, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, p, pub) &*&
               p == pair_item(_, _); @*/
{
  if (!is_pair(item))
    abort_crypto_lib("Presented item is not a pair item");
}

struct item *create_pair(struct item *first, struct item *second)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               [?f1]item(first, ?f, pub) &*& [?f2]item(second, ?s, pub); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               [f1]item(first, f, pub) &*& [f2]item(second, s, pub) &*&
               item(result, pair_item(f, s), pub); @*/
{
  //@ open [f0]world(pub, key_clsfy);
  char* temp;
  struct item* pair = malloc(sizeof(struct item));
  if (pair == 0){abort_crypto_lib("malloc of item failed");}

  //@ open [f1]item(first, f, pub);
  //@ assert [f1]first->content |-> ?cont_f &*& [f1]first->size |-> ?size_f;
  //@ assert [f1]crypto_chars(secret, cont_f, size_f, ?ccs_f);
  //@ assert [_]item_constraints(f, ccs_f, pub);
  //@ well_formed_item_constraints(f, f);
  //@ open [_]well_formed_item_ccs(f)(ccs_f);
  //@ open [f2]item(second, s, pub);
  //@ assert [f2]second->content |-> ?cont_s &*& [f2]second->size |-> ?size_s;
  //@ assert [f2]crypto_chars(secret, cont_s, size_s, ?ccs_s);
  //@ well_formed_item_constraints(s, s);
  //@ open [_]well_formed_item_ccs(s)(ccs_s);
  //@ assert [_]item_constraints(s, ccs_s, pub);
  if (INT_MAX - TAG_LENGTH - (int) sizeof(int) - first->size < second->size)
    abort_crypto_lib("Requested pair item was to big");
  pair->size = TAG_LENGTH + (int) sizeof(int) + first->size + second->size;
  pair->content = malloc_wrapper(pair->size);
  //@ assert pair->content |-> ?cont &*& pair->size |-> ?size;
  write_tag(pair->content, TAG_PAIR);

  //@ assert chars(cont, TAG_LENGTH, full_tag(TAG_PAIR));
  //@ public_chars(cont, TAG_LENGTH);
  temp = pair->content + TAG_LENGTH;
  //@ chars__split(cont + TAG_LENGTH, sizeof(int));
  //@ assert [f1]integer(&first->size, ?flen);
  //@ integer_to_chars(&first->size);
  //@ open chars((void*) &first->size, sizeof(int), chars_of_int(flen));
  //@ character_limits((void*) &first->size);
  //@ close [f1]chars((void*) &first->size, sizeof(int), chars_of_int(flen));
  //@ public_chars((void*) &first->size, sizeof(int));
  //@ public_chars((void*) &first->size, sizeof(int));
  //@ chars_to_crypto_chars((void*) &first->size, sizeof(int));
  write_buffer(&temp, (void*) &(first->size), (int) sizeof(int));
  //@ cs_to_ccs_crypto_chars((void*) &first->size, chars_of_int(flen));
  //@ cs_to_ccs_crypto_chars(temp - sizeof(int), chars_of_int(flen));
  //@ chars_to_secret_crypto_chars(temp - sizeof(int), sizeof(int));
  //@ chars_to_integer(&first->size);
  //@ chars__split(cont + TAG_LENGTH + sizeof(int), first->size);
  write_buffer(&temp, first->content, first->size);
  write_buffer(&temp, second->content, second->size);
  //@ crypto_chars_join(cont + TAG_LENGTH + sizeof(int));
  //@ crypto_chars_join(cont + TAG_LENGTH);

  //@ list<crypto_char> size_f_ccs = cs_to_ccs(chars_of_int(size_f));
  //@ list<crypto_char> ccs0 = append(size_f_ccs, append(ccs_f, ccs_s));
  //@ list<crypto_char> ccs_tag = full_ctag(c_to_cc(TAG_PAIR));
  //@ list<crypto_char> ccs = append(ccs_tag, ccs0);
  //@ assert length(size_f_ccs) == sizeof(int);

  //@ take_append(sizeof(int), size_f_ccs, append(ccs_f, ccs_s));
  //@ drop_append(sizeof(int), size_f_ccs, append(ccs_f, ccs_s));
  //@ take_append(size_f, ccs_f, ccs_s);
  //@ drop_append(size_f, ccs_f, ccs_s);
  //@ assert drop(sizeof(int), ccs0) == append(ccs_f, ccs_s);
  //@ assert size_f_ccs == cs_to_ccs(chars_of_unbounded_int(length(ccs_f)));
  //@ append_assoc(size_f_ccs, ccs_f, ccs_s);
  //@ item p = pair_item(f, s);
  //@ close ic_pair(p)(ccs_f, ccs_s);
  //@ length_equals_nat_length(ccs);
  //@ length_equals_nat_length(ccs0);
  //@ drop_drop(sizeof(int), TAG_LENGTH, ccs);
  /*@ switch(nat_length(ccs))
      {
        case succ(n):
          well_formed_upper_bound(nat_length(ccs_f), n, ccs_f);
          well_formed_upper_bound(nat_length(ccs_s), n, ccs_s);
          get_forall_t<char>();
          get_forall_t<list<char> >();
          assert FORALLP_C &*& FORALLP_CS;
          fixpoint(list<crypto_char>, bool) wf =
            (well_formed_ccs)(forallc, forallcs, n);
          if (!exists_t<char>(forallc,
                (well_formed_pair)(forallcs, wf, ccs0)))
          {
            if (!exists_t<list<char> >(forallcs,
                (well_formed_pair_bounded)(wf, ccs0)))
            {
              forall_t_elim(forallcs, (notf)((well_formed_pair_bounded)(wf, ccs0)),
                            chars_of_int(size_f));
            }
            forall_t_elim(forallc, (notf)((well_formed_pair)(forallcs, wf, ccs0)),
                          head(chars_of_int(size_f)));
          }
        case zero:
          assert false;
      }
  @*/
  //@ CLOSE_ITEM_CONSTRAINTS(cont, TAG_PAIR, size, p)
  //@ close item(pair, p, pub);

  //@ close [f1]item(first, f, pub);
  //@ close [f2]item(second, s, pub);
  return pair;
  //@ close [f0]world(pub, key_clsfy);
}

void pair_get_components(struct item* pair,
                         struct item** firstp, struct item** secondp)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& item(pair, ?p, pub) &*&
               p == pair_item(?f0, ?s0) &*&
               *firstp |-> _ &*& *secondp |-> _; @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(pair, p, pub) &*&
               pointer(firstp, ?fp) &*& pointer(secondp, ?sp) &*&
                item(fp, ?f1, pub) &*& item(sp, ?s1, pub) &*&
               col ? true : f0 == f1 && s0 == s1; @*/
{
  char* temp;

  check_is_pair(pair);
  //@ open item(pair, p, pub);
  //@ assert pair->content |-> ?cont &*& pair->size |-> ?size;
  //@ assert crypto_chars(secret, cont, size, ?ccs);
  //@ OPEN_ITEM_CONSTRAINTS(p, ccs, pub)
  //@ assert [_]ic_parts(p)(?ccs_tag, ?ccs_cont);
  //@ assert [_]ic_pair(p)(?ccs_f, ?ccs_s);

  struct item *first  = malloc(sizeof(struct item));
  struct item *second = malloc(sizeof(struct item));
  if (first == 0 || second == 0){abort_crypto_lib("malloc of item failed");}

  temp = pair->content;
  //@ crypto_chars_split(cont, TAG_LENGTH);
  //@ if (col) public_ccs_split(ccs, TAG_LENGTH);
  //@ assert crypto_chars(secret, temp, TAG_LENGTH, ccs_tag);
  //@ assert crypto_chars(secret, temp + TAG_LENGTH, size - TAG_LENGTH, ccs_cont);
  temp = temp + TAG_LENGTH;
  if (pair->size <= TAG_LENGTH + (int) sizeof(int))
    abort_crypto_lib("Found corrupted pair item 1"); //~allow_dead_code

  //@ open [f]world(pub, key_clsfy);
  //@ crypto_chars_split(temp, sizeof(int));
  //@ if (col) public_ccs_split(ccs_cont, sizeof(int));
  //@ assert crypto_chars(secret, temp, sizeof(int), ?ccs_size_f);
  //@ assert crypto_chars(secret, temp + sizeof(int), size - TAG_LENGTH - sizeof(int), ?ccs_p);
  //@ take_append(sizeof(int), ccs_size_f, ccs_p);
  //@ drop_append(sizeof(int), ccs_size_f, ccs_p);
  //@ cs_to_ccs_crypto_chars(temp, chars_of_int(length(ccs_f)));
  //@ chars_to_integer(temp);
  first->size = *((int*) (void*) temp);
  second->size = pair->size - TAG_LENGTH - (int) sizeof(int) - first->size;
  //@ assert first->size |-> ?size_f &*& second->size |-> ?size_s;
  if (first->size <= TAG_LENGTH ||
      pair->size - TAG_LENGTH - (int) sizeof(int) <= first->size)
    abort_crypto_lib("Found corrupted pair item 2");
  //@ integer_to_chars(temp);
  temp = temp + (int) sizeof(int);
  //@ assert ccs_cont == append(ccs_size_f, ccs_p);
  //@ append_assoc(ccs_cont, ccs_size_f, ccs_p);
  //@ crypto_chars_split(temp, first->size);
  //@ if (col) public_ccs_split(ccs_p, first->size);
  //@ take_append(size_f, ccs_f, ccs_s);
  //@ drop_append(size_f, ccs_f, ccs_s);
  //@ assert crypto_chars(secret, temp, size_f, ccs_f);
  //@ assert crypto_chars(secret, temp + size_f, size_s, ccs_s);
  //@ assert ccs_p == append(ccs_f, ccs_s);
  first->content = malloc_wrapper(first->size);
  if (first->size <= MINIMAL_STRING_SIZE)
    abort_crypto_lib("Found corrupted pair item 3"); //~allow_dead_code
  crypto_memcpy(first->content, temp, (unsigned int) first->size);
  temp = temp + first->size;
  if (second->size <= MINIMAL_STRING_SIZE)
    abort_crypto_lib("Found corrupted pair item 4");
  second->content = malloc_wrapper(second->size);
  crypto_memcpy(second->content, temp, (unsigned int) second->size);
  //@ crypto_chars_join(cont + TAG_LENGTH + sizeof(int));
  //@ chars_to_secret_crypto_chars(cont + TAG_LENGTH, sizeof(int));
  //@ crypto_chars_join(cont + TAG_LENGTH);
  //@ assert first->content |-> ?cont_f &*& second->content |-> ?cont_s;
  //@ assert crypto_chars(secret, cont_f, size_f, ccs_f);
  //@ assert crypto_chars(secret, cont_s, size_s, ccs_s);
  //@ assert cs_to_ccs(chars_of_unbounded_int(size_f)) == ccs_size_f;
  //@ assert length(ccs_f) == size_f;
  //@ assert [_]item_constraints(f0, ?ccs_f0, pub);
  //@ assert [_]item_constraints(s0, ?ccs_s0, pub);
  //@ drop_append(sizeof(int), ccs_size_f, append(ccs_f0, ccs_s0));
  //@ take_append(sizeof(int), ccs_size_f, append(ccs_f0, ccs_s0));
  //@ drop_append(length(ccs_f0), ccs_f0, ccs_s0);
  //@ take_append(length(ccs_f0), ccs_f0, ccs_s0);
  //@ close item(first, f0, pub);
  //@ close item(second, s0, pub);
  //@ close item(pair, pair_item(f0, s0), pub);

  *firstp = first;
  *secondp = second;
  //@ close [f]world(pub, key_clsfy);
}

struct item *pair_get_first(struct item *pair)
  //@ requires [?f0]world(?pub, ?key_clsfy) &*& item(pair, ?p, pub);
  /*@ ensures  [f0]world(pub, key_clsfy) &*& item(pair, p, pub) &*&
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
  //@ requires [?f0]world(?pub, ?key_clsfy) &*& item(pair, ?p, pub);
  /*@ ensures  [f0]world(pub, key_clsfy) &*&item(pair, p, pub) &*&
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
