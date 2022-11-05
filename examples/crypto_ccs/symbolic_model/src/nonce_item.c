#include "nonce_item.h"

#include "principal_ids.h"
#include "item_constraints.h"
#include "invariants.h"
#include "serialization.h"

struct havege_state random_state;

/*@
predicate nonces_initialized() =
  havege_state_initialized(&random_state)
;

predicate nonces_state(void *state) = state == &random_state;
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
  //@ ensures  [f]havege_state_initialized(result) &*& [_]nonces_state(result);
{
  //@ open [f]nonces_initialized();
  return &random_state;
  //@ close nonces_state(&random_state);
  //@ leak nonces_state(_);
}

void nonces_hide_state(void* state)
  //@ requires [?f]havege_state_initialized(state) &*& [_]nonces_state(state);
  //@ ensures  [f]nonces_initialized();
{
  //@ open nonces_state(state);
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
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == nonce_item(_, _, _) : true; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open item(item, i, pub);
  //@ open [_]item_constraints(i, ?cs, pub);
  return item_tag(item->content, item->size) == TAG_NONCE;
  //@ close item(item, i, pub);
  //@ close [f]world(pub, key_clsfy);
}

void check_is_nonce(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == nonce_item(_, _, _); @*/
{
  if (!is_nonce(item))
    abort_crypto_lib("Presented item is not a nonce");
}

struct item *create_nonce()
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal, ?count) &*&
               nonce_request(principal, ?info); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal, count + 1) &*&
               item(result, ?i, pub) &*& info_for_item(i) == info &*&
               i == nonce_item(principal, count + 1, 0); @*/
{
  //@ open [f]world(pub, key_clsfy);
  struct item* item = malloc(sizeof(struct item));
  if (item == 0){abort_crypto_lib("malloc of item failed");}
  item->size = TAG_LENGTH + 1 + NONCE_SIZE;
  item->content = malloc_wrapper(item->size);
  //@ assert item->content |-> ?cont;
  //@ assert item->size |-> ?size;
  write_tag(item->content, TAG_NONCE);
  //@ assert chars(cont, TAG_LENGTH, ?cs_tag);
  //@ assert cs_tag == full_tag(TAG_NONCE);
  *(item->content + TAG_LENGTH) = 0;
  //@ assert chars(cont + TAG_LENGTH, 1, cons(0, nil));
  //@ public_cs(cons(0, nil));
  //@ chars_to_secret_crypto_chars(cont + TAG_LENGTH, 1);
  //@ close [f]world(pub, key_clsfy);
  create_havege_random(item->content + TAG_LENGTH + 1, NONCE_SIZE);

  //@ open cryptogram(cont + TAG_LENGTH + 1, NONCE_SIZE, ?n_ccs, ?n_cg);
  //@ assert n_cg == cg_nonce(principal, count + 1);
  //@ item nonce = nonce_item(principal, count + 1, 0);
  //@ list<crypto_char> ccs_cont = cons(c_to_cc(0), n_ccs);
  //@ crypto_chars_join(cont + TAG_LENGTH);
  //@ close ic_cg(nonce)(n_ccs, n_cg);
  //@ CLOSE_ITEM_CONSTRAINTS(cont, TAG_NONCE, size, nonce)
  //@ close item(item, nonce, pub);
  return item;

}

void increment_nonce(struct item *item)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               item(item, ?i, pub) &*&
               i == nonce_item(?principal, ?count, ?inc0); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               item(item, ?i_inc, pub) &*&
               col ? true :
                 i_inc == nonce_item(principal, count, inc0 + 1) &&
                 info_for_item(i) == info_for_item(i_inc); @*/
{
  //@ open  item(item, i, pub);
  //@ assert item->size |-> ?size &*& item->content |-> ?cont;
  //@ assert [_]item_constraints(i, ?ccs, pub);
  //@ OPEN_ITEM_CONSTRAINTS(i, ccs, pub)
  //@ open [_]ic_parts(i)(?ccs_tag, ?ccs_cont);
  //@ crypto_chars_split(cont, TAG_LENGTH);
  //@ assert crypto_chars(secret, cont, TAG_LENGTH, ccs_tag);
  //@ assert crypto_chars(secret, cont + TAG_LENGTH, size - TAG_LENGTH, ccs_cont);
  //@ cs_to_ccs_crypto_chars(cont, full_tag(TAG_NONCE));
  //@ crypto_chars_split(cont + TAG_LENGTH, 1);
  //@ assert crypto_chars(secret, cont + TAG_LENGTH, 1, cons(?cc_inc1, nil));
  //@ assert crypto_chars(secret, cont + TAG_LENGTH + 1, size - TAG_LENGTH - 1, ?n_ccs);
  //@ take_append(1, cons(cc_inc1, nil), n_ccs);
  //@ drop_append(1, cons(cc_inc1, nil), n_ccs);
  //@ assert ccs_cont == cons(cc_inc1, n_ccs);
  //@ open [f]world(pub, key_clsfy);
  //@ public_crypto_chars(cont + TAG_LENGTH, 1);
  char *increment = item->content + TAG_LENGTH;
  //@ chars_limits(cont + TAG_LENGTH);
  //@ open chars(cont + TAG_LENGTH, 1, cons(?inc1, _));
  //@ c_to_cc_inj(inc0, inc1);
  //@ assert cc_inc1 == c_to_cc(inc1);
  if (*increment < 0 || *increment >= 126)
    abort_crypto_lib("Incremented nonce to many times");
  (*increment)++;
  //@ close chars(cont + TAG_LENGTH, 1, cons(inc1 + 1, _));
  //@ public_cs(cons(inc1 + 1, nil));
  //@ close [f]world(pub, key_clsfy);
  //@ chars_to_secret_crypto_chars(cont + TAG_LENGTH, 1);
  //@ crypto_chars_join(cont + TAG_LENGTH);

  //@ item nonce = nonce_item(principal, count, inc1 + 1);
  //@ list<crypto_char> nonce_cont = cons(c_to_cc(inc1 + 1), n_ccs);
  //@ list<crypto_char> nonce_ccs = append(ccs_tag, nonce_cont);
  //@ take_append(1, cons(c_to_cc(inc1 + 1), nil), n_ccs);
  //@ drop_append(1, cons(c_to_cc(inc1 + 1), nil), n_ccs);
  //@ assert [_]ic_cg(i)(n_ccs, ?n_cg);
  //@ close ic_cg(nonce)(n_ccs, n_cg);
  //@ CLOSE_ITEM_CONSTRAINTS(cont, TAG_NONCE, size, nonce)
  //@ close item(item, nonce, pub);
}

void create_havege_random(char *output, int len)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               nonce_request(?principal, ?info) &*&
               principal(principal, ?count) &*&
               chars_(output, len, _);  @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal, count + 1) &*&
               cryptogram(output, len, ?cs, ?cg) &*&
               cg == cg_nonce(principal, count + 1) &*&
               info == cg_info(cg); @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open nonce_request(principal, info);
  //@ open [f]nonces_initialized();
  //@ close random_request(principal, info, false);
  //@ open principal(principal, count);
  if (len < MIN_RANDOM_SIZE)
    abort_crypto_lib("Trying to generate a random value that is to small");
  if (havege_random((void*) &random_state, output, (unsigned int) len) != 0)
    abort_crypto_lib("Generation of random value failed");
  //@ close principal(principal, count + 1);
  //@ close [f]nonces_initialized();
  //@ close [f]world(pub, key_clsfy);
}

void random_buffer(char* buffer, int size)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               chars_(buffer, size, _) &*&
               principal(?principal, ?count) &*&
               [_]pub(nonce_item(principal, count + 1, 0)); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               chars(buffer, size, _) &*&
               principal(principal, count + 1); @*/
{
  //@ close nonce_request(principal, 0);
  create_havege_random(buffer, size);
  //@ assert cryptogram(buffer, size, ?cs, ?cg);
  //@ assert cg == cg_nonce(principal, count + 1);
  //@ close polarssl_pub(pub)(cg);
  //@ leak polarssl_pub(pub)(cg);
  //@ open [f]world(pub, key_clsfy);
  //@ public_cryptogram(buffer, cg);
  //@ close [f]world(pub, key_clsfy);
}

int random_int()
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal, ?count) &*&
               [_]pub(nonce_item(principal, count + 1, 0)); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal, count + 1); @*/
{
  int i;
  //@ int__to_chars_(&i);
  random_buffer((void*) &i, (int) sizeof(int));
  //@ chars_to_integer(&i);
  return i;
}

unsigned int random_u_int()
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal, ?count)  &*&
               [_]pub(nonce_item(principal, count + 1, 0)); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal, count + 1); @*/
{
  unsigned int i;
  //@ uint__to_chars_(&i);
  random_buffer((void*) &i, (int) sizeof(unsigned int));
  //@ chars_to_u_integer(&i);
  return i;
}
