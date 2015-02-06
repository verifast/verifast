#include "nonce_item.h"

#include "principals.h"
#include "item_constraints.h"
#include "serialization.h"

struct havege_state random_state;

/*@
predicate nonces_initialized() =
  havege_state_initialized(&random_state)
;
@*/

void nonces_init()
  //@ requires module(nonce_item, true);
  //@ ensures  nonces_initialized();
{
  //@ open_module();
  //@ close havege_state(&random_state);
  havege_init(&random_state);
  //@ close nonces_initialized();
}

void *nonces_expose_state()
  //@ requires [?f]nonces_initialized();
  //@ ensures  [f]havege_state_initialized(result);
{
  //@ open [f]nonces_initialized();
  return &random_state;
}

void nonces_hide_state(void* state)
  //@ requires [?f]havege_state_initialized(state);
  //@ ensures  [f]nonces_initialized();
{
  void *temp = &random_state;
  if (state != temp)
    abort_crypto_lib("Illegal state for nonces");
  
  //@ close [f]nonces_initialized();
}

void nonces_exit()
  //@ requires nonces_initialized();
  //@ ensures  module(nonce_item, false);
{
  //@ open nonces_initialized();
  havege_free(&random_state);
  //@ open havege_state(&random_state);
  //@ close_module();
}

bool is_nonce(struct item *item)
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == nonce_item(_, _, _) : true; @*/
{
  //@ open item(item, i, pub);
  //@ assert item->content |-> ?cont;
  //@ open chars(cont, ?size, ?cs);
  //@ open [_]item_constraints(?b, i, cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(i, cs, pub);
  return *(item->content) == 'c';
  //@ close chars(cont, size, cs);
  //@ close item(item, i, pub);
}

void check_is_nonce(struct item *item)
  //@ requires item(item, ?i, ?pub);
  //@ ensures  item(item, i, pub) &*& i == nonce_item(_, _, _);
{
  if (!is_nonce(item))
    abort_crypto_lib("Presented item is not a nonce");
}

struct item *create_nonce()
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal, ?count) &*&
               nonce_request(principal, ?info); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal, count + 1) &*&
               item(result, ?i, pub) &*& [_]info_for_item(i, info) &*&
               i == nonce_item(principal, count + 1, 0); @*/
{
  struct item* item = malloc(sizeof(struct item));
  if (item == 0){abort_crypto_lib("malloc of item failed");}
  item->size = 2 + NONCE_SIZE;
  item->content = malloc_wrapper(item->size);
  *(item->content) = 'c';
  *(item->content + 1) = 0;
  create_havege_random(item->content + 2, NONCE_SIZE);
  
  //@ item nonce = nonce_item(principal, count + 1, 0);
  //@ assert item->content |-> ?cont;
  //@ open polarssl_cryptogram(cont + 2, NONCE_SIZE, ?n_cs, ?n_cg);
  //@ close exists(pair(principal, count + 1));
  //@ list<char> cs = cons('c', cons(0, n_cs));
  //@ close item_constraints_no_collision(nonce, cs, pub);
  //@ leak item_constraints_no_collision(nonce, cs, pub);
  //@ close item_constraints(false, nonce, cs, pub);
  //@ leak item_constraints(false, nonce, cs, pub);
  //@ close item(item, nonce, pub);
  //@ close info_for_item(nonce, info);
  //@ leak info_for_item(nonce, info);
  return item;
}

void increment_nonce(struct item *item)
  /*@ requires item(item, ?i, ?pub) &*& 
               i == nonce_item(?principal, ?count, ?inc0); @*/
  /*@ ensures  item(item, ?i_inc, pub) &*& 
               [_]info_for_item(i, ?info1) &*&
               [_]info_for_item(i_inc, ?info2) &*&
               collision_in_run() ? 
                 true 
               : 
                 i_inc == nonce_item(principal, count, inc0 + 1) &&
                 info1 == info2; @*/
{
  //@ open  item(item, i, pub);
  //@ assert item->size |-> ?size &*& item->content |-> ?cont;
  //@ chars_limits(cont);
  //@ open chars(cont, size, ?cs);
  //@ open [_]item_constraints(?b, i, cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(i, cs, pub);
  
  char *increment = item->content + 1;
  //@ open chars(cont + 1, size - 1, _);
  //@ assert chars(cont + 2, size - 2, ?n_cs);
  if (*increment < 0 || *increment >= 126)
    abort_crypto_lib("Incremented nonce to many times");
  (*increment)++;
  //@ assert character(increment, ?val);
  //@ close chars(cont + 1, size - 1, cons(val, n_cs));
  //@ close chars(cont, size, cons('c', cons(val, n_cs)));
  
  //@ item nonce;
  //@ list<char> nonce_prefix = cons('c', cons(val, nil)); 
  //@ list<char> nonce_cs = append(nonce_prefix, n_cs);
  /*@ if (!b) 
      {
        nonce = nonce_item(principal, count, inc0 + 1);
        open [_]item_constraints_no_collision(i, cs, pub);
        assert val == inc0 + 1;
        close item_constraints_no_collision(nonce, nonce_cs, pub);
        leak item_constraints_no_collision(nonce, nonce_cs, pub);
        item_constraints_no_collision_well_formed(nonce, nonce);
      }
      else
      {
        nonce = dummy_item_for_tag('c');
        polarssl_generated_public_cryptograms_subset(polarssl_pub(pub), cs);
        polarssl_cryptograms_in_chars_public_upper_bound_split(
                                                      polarssl_pub(pub), cs, 2);
        collision_public(pub, nonce_cs);
        polarssl_cryptograms_in_chars_public_upper_bound_join(polarssl_pub(pub), 
                                                              nonce_cs, n_cs);
        polarssl_cryptograms_in_chars_upper_bound_from(nonce_cs, 
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
      }
  @*/
  //@ close item_constraints(b, nonce, nonce_cs, pub);
  //@ leak item_constraints(b, nonce, nonce_cs, pub);
  //@ close item(item, nonce, pub);
  //@ close info_for_item(i, polarssl_info_for_item(i));
  //@ leak info_for_item(i, polarssl_info_for_item(i));
  //@ close info_for_item(nonce, polarssl_info_for_item(nonce));
  //@ leak info_for_item(nonce, polarssl_info_for_item(nonce));
}

/*@
lemma void info_for_incremented_nonce(item i, int inc1, int inc2)
  requires [_]info_for_item(i, ?info) &*&
           i == nonce_item(?p, ?c, inc1);
  ensures  [_]info_for_item(nonce_item(p, c, inc2), info);
{
  open [_]info_for_item(i, info);
  item i2 = nonce_item(p, c, inc2);
  close info_for_item(i2, info);
  leak info_for_item(i2, info);
}
@*/

void create_havege_random(char *output, int len)
  /*@ requires [?f]world(?pub) &*& 
               nonce_request(?principal, ?info) &*&
               generated_values(principal, ?count) &*&
               chars(output, len, _);  @*/
  /*@ ensures  [f]world(pub) &*& 
               generated_values(principal, count + 1) &*&
               polarssl_cryptogram(output, len, ?cs, ?cg) &*& 
               cg == polarssl_random(principal, count + 1) &*&
               info == polarssl_cryptogram_info(cg); @*/
{
  //@ open [f]world(pub);
  //@ open nonce_request(principal, info);
  //@ open generated_values(principal, count);
  //@ open [f]nonces_initialized();
  //@ close random_request(principal, info, false);
  if (len < POLARSSL_MIN_RANDOM_BYTE_SIZE)
    abort_crypto_lib("Trying to generate a random value that is to small");
  if (havege_random((void*) &random_state, output, (unsigned int) len) != 0)
    abort_crypto_lib("Generation of random value failed");
  //@ close [f]nonces_initialized();
  //@ close generated_values(principal, count + 1);
  //@ close [f]world(pub);
}

void random_buffer(char* buffer, int size)
  /*@ requires [?f]world(?pub) &*&
               chars(buffer, size, _) &*&
               generated_values(?principal, ?count); @*/
  /*@ ensures  [f]world(pub) &*&
               chars(buffer, size, _) &*&
               generated_values(principal, count + 1); @*/
{
  //@ close nonce_request(principal, 0);
  create_havege_random(buffer, size);
  //@ open polarssl_cryptogram(buffer, size, _, _);
}

int random_int()
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal, ?count); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal, count + 1); @*/
{
  int i;
  random_buffer((void*) &i, (int) sizeof(int));
  //@ chars_to_integer(&i);
  return i;
}

unsigned int random_u_int()
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal, ?count); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal, count + 1); @*/
{
  unsigned int i;
  random_buffer((void*) &i, (int) sizeof(unsigned int));
  //@ chars_to_u_integer(&i);
  return i;
}
