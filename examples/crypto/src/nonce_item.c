#include "nonce_item.h"
#include "principals.h"

struct havege_state random_state;

/*@

predicate nonces_initialized() =
  havege_state_initialized(&random_state)
;

@*/

void nonces_init()
  /*@ requires [?f]polarssl_world<item>(?pub) &*&
               module(nonce_item, true); @*/
  /*@ ensures  [f]polarssl_world<item>(pub) &*& 
               nonces_initialized(); @*/
{
  //@ open_module();
  //@ close havege_state(&random_state);
  havege_init(&random_state);
  //@ close nonces_initialized();
}

void *nonces_expose_state()
  /*@ requires [?f1]polarssl_world<item>(?pub) &*&
               [?f2]nonces_initialized(); @*/
  /*@ ensures  [f1]polarssl_world<item>(pub) &*& 
               [f2]havege_state_initialized(result); @*/
{
  //@ open [f2]nonces_initialized();
  return &random_state;
}

void nonces_hide_state(void* state)
  /*@ requires [?f1]polarssl_world<item>(?pub) &*&
               [?f2]havege_state_initialized(state); @*/
  /*@ ensures  [f1]polarssl_world<item>(pub) &*& 
               [f2]nonces_initialized(); @*/
{
  void *temp = &random_state;
  if (state != temp)
    abort_crypto_lib("Illegal state for nonces");
  
  //@ close [f2]nonces_initialized();
}

void nonces_exit()
  /*@ requires [?f]polarssl_world<item>(?pub) &*&
               nonces_initialized(); @*/
  /*@ ensures  [f]polarssl_world<item>(pub) &*&
               module(nonce_item, false); @*/
{
  //@ open nonces_initialized();
  //@ havege_exit(&random_state);
  //@ open havege_state(&random_state);
  //@ close_module();
}

struct item *create_nonce()
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal, ?count) &*&
               nonce_request(principal, ?info); @*/
  /*@ ensures  [f]world(pub) &*& 
               generated_values(principal, count + 1) &*&
               item(result, ?i) &*&
               i == nonce_item(principal, count + 1, 0, info); 
  @*/
{
  int increment = 0;
  char* temp;
  
  struct item* nonce = malloc(sizeof(struct item));
  if (nonce == 0){abort_crypto_lib("malloc of item failed");}
  nonce->tag = 2;
  nonce->size = NONCE_SIZE + (int) sizeof(int);
  nonce->content = malloc_wrapper(nonce->size);
  temp = nonce->content;
  
  write_buffer(&temp, (void*) &increment, (int) sizeof(int));
  create_havege_random(temp, NONCE_SIZE);
  
  //@ open [f]world(pub);
  //@ havege_polarssl_item_to_chars(temp);
  //@ close item(nonce, nonce_item(principal, count + 1, 0, info));
  return nonce;
  //@ close [f]world(pub);
}

bool is_nonce(struct item *item)
  //@ requires item(item, ?i);
  /*@ ensures  item(item, i) &*&
        switch (i)
        {
          case data_item(d0):
            return result == false;
          case pair_item(f0, s0):
            return result == false;
          case nonce_item(p0, c0, inc0, i0):
            return result == true;
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
  return (item->tag == 2);
  //@ close item(item, i);
}

void check_is_nonce(struct item *item)
  //@ requires item(item, ?i);
  /*@ ensures
        switch (i)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return false;
          case nonce_item(p0, c0, inc0, i0):
            return item(item, nonce_item(p0, c0, inc0, i0));
          case key_item(p0, c0, k0, i0):
            return false;
          case hmac_item(k0, pay0):
            return false;
          case encrypted_item(k0, pay0, ent0):
            return false;
        };
  @*/
{
  if (!is_nonce(item))
    abort_crypto_lib("Presented item is not a nonce");
}

void increment_nonce(struct item *item)
  /*@ requires [?f]world(?pub) &*&
               item(item, ?ni) &*& 
               ni == nonce_item(?principal, ?count, ?inc0, ?info);
  @*/
  /*@ ensures  [f]world(pub) &*&
               item(item, ?i) &*& 
               i == nonce_item(principal, count, inc0 + 1, info);
  @*/
{
  //@ open  item(item, nonce_item(principal, count, inc0, info));
  //@ assert item->size |-> ?size;
  //@ assert item->content |-> ?content &*& chars(content, size, ?cs);
  int *increment = (void*) item->content;
  if (item->size < (int) sizeof(int))
     abort_crypto_lib("Nonce to increment was corrupted");
  //@ chars_split((void*) increment, sizeof(int));
  /*@
      if (!collision_in_run())
      {
        take_append(sizeof(int), chars_of_int(inc0),  
                          havege_chars_for_polarssl_item(
                          polarssl_havege_item(principal, count)));
        drop_append(sizeof(int), chars_of_int(inc0),  
                          havege_chars_for_polarssl_item(
                          polarssl_havege_item(principal, count)));
      }
  @*/
  //@ chars_to_integer(increment);
  if (*increment == INT_MAX)
     abort_crypto_lib("Incremented nonce to many times");
  (*increment)++;
  //@ integer_to_chars(increment);
  //@ close item(item, nonce_item(principal, count, inc0 + 1, info));
}

void random_buffer(char* buffer, int size)
  /*@ requires [?f]world(?pub) &*&
               chars(buffer, size, _) &*&
               generated_values(?principal, ?count); @*/
  /*@ ensures  [f]world(pub) &*&
               chars(buffer, size, _) &*&
               generated_values(principal, count + 1); @*/
{
  //@ open [f]world(pub);
  //@ open generated_values(principal, count);

  //@ open [f]nonces_initialized();
  //@ close havege_request(principal, 0);
  havege_random((void*) &random_state, buffer, (unsigned int) size);
  //@ havege_polarssl_item_to_chars(buffer);
  //@ close [f]nonces_initialized();
  
  //@ close generated_values(principal, count + 1);
  //@ close [f]world(pub);
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

void create_havege_random/*@ <T> @*/(char *output, int len)
  /*@ requires
        [?f0]world(?pub) &*& 
        nonce_request(?principal, ?info) &*&
        generated_values(principal, ?count) &*&
        chars(output, len, _);
  @*/
  /*@ ensures
        [f0]world(pub) &*& 
        generated_values(principal, count + 1) &*&
        polarssl_item(output, ?i) &*& 
        i == polarssl_havege_item(principal, count + 1) &*&
        len == length(havege_chars_for_polarssl_item(i)) &*&
        info == info_for_polarssl_item(i);
  @*/
{
  //@ open [f0]world(pub);
  //@ open nonce_request(principal, info);
  //@ open generated_values(principal, count);
  //@ open [f0]nonces_initialized();
  //@ close havege_request(principal, info);
  havege_random((void*) &random_state, output, (unsigned int) len);
  //@ close [f0]nonces_initialized();
  //@ close generated_values(principal, count + 1);
  //@ close [f0]world(pub);
}
  

