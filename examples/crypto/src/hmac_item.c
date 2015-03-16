#include "hmac_item.h"

#include "key_item.h"
#include "principals.h"
#include "item_constraints.h"
#include "serialization.h"

bool is_hmac(struct item *item)
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == hmac_item(_, _, _) : true; @*/
{
  //@ open item(item, i, pub);
  //@ open chars(item->content, ?size, ?cs);
  //@ open [_]item_constraints(?b, i, cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(i, cs, pub);
  return *(item->content) == 'h';
  //@ close item(item, i, pub);
}

void check_is_hmac(struct item *item)
  //@ requires item(item, ?i, ?pub);
  //@ ensures  item(item, i, pub) &*& i == hmac_item(_, _, _);
{
  if (!is_hmac(item))
    abort_crypto_lib("Presented item is not an hmac");
}

struct item *create_hmac(struct item *key, struct item *payload)
  /*@ requires [?f]world(?pub) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*& 
               k == symmetric_key_item(?creator, ?id); @*/
  /*@ ensures  [f]world(pub) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*& 
               item(result, ?hmac, pub) &*& 
               collision_in_run() ? 
                 true
               :
                 hmac == hmac_item(creator, id, some(pay)); @*/
{
  //@ open item(payload, pay, pub);
  //@ open [_]item_constraints(_, pay, ?pay_cs, pub);
  //@ open item(key, k, pub);
  check_valid_symmetric_key_item_size(key->size);
  //@ assert key->content |-> ?k_cont;
  //@ assert chars(k_cont + 1, GCM_KEY_SIZE, ?k_cs);
  //@ open [_]item_constraints(?b, k, ?key_cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(k, key_cs, pub);
  
  struct item* hmac = malloc(sizeof(struct item));
  if (hmac == 0){abort_crypto_lib("malloc of item failed");}
  
  hmac->size = 1 + HMAC_SIZE;
  hmac->content = malloc_wrapper(hmac->size);
  *(hmac->content) = 'h';
  
  check_valid_symmetric_key_item_size(key->size);
  //@ chars_limits(key->content);
  //@ polarssl_cryptogram k_cg = polarssl_symmetric_key(creator, id);
  //@ close polarssl_key_id(creator, id);
  //@ open [f]world(pub);
  if (payload->size < POLARSSL_MIN_HMAC_INPUT_BYTE_SIZE)
    {abort_crypto_lib("Payload of hmac was to small");}
  sha512_hmac(key->content + 1, (unsigned int) GCM_KEY_SIZE, 
              payload->content, (unsigned int) payload->size, 
              hmac->content + 1, 0);
  //@ close [f]world(pub);
  //@ assert hmac->content |-> ?cont &*& hmac->size |-> ?size;
  /*@ if (collision_in_run())
      {
        if (k_cs == polarssl_chars_for_cryptogram(k_cg))
          open polarssl_cryptogram(cont + 1, 64, _, _);
        else
          open polarssl_public_message(polarssl_pub(pub))(cont + 1, 64, _);
          
        item h = dummy_item_for_tag('h');
        assert chars(cont, size, ?cs);
        collision_public(pub, cs);
        close item_constraints(true, h, cs, pub);
        leak item_constraints(true, h, cs, pub);
        close item(hmac, h, pub);
      }
      else
      {
        assert k_cs == polarssl_chars_for_cryptogram(k_cg);
        
        item h = hmac_item(creator, id, some(pay));
        assert key_cs == cons('e', k_cs);
        assert k_cs == polarssl_chars_for_cryptogram(k_cg);
        open polarssl_cryptogram(cont + 1, 64, ?h_cs, ?h_cg);
        list<char> cs = cons('h', h_cs);
        assert chars(cont, size, cs);
        assert h_cg == polarssl_hmac(creator, id, pay_cs);
        item_constraints_well_formed(pay, h);
        close item_constraints_no_collision(h, cs, pub);
        leak item_constraints_no_collision(h, cs, pub);
        close item_constraints(false, h, cs, pub);
        leak item_constraints(false, h, cs, pub);
        close item(hmac, h, pub);
      }
  @*/
  
  return hmac;
  
  //@ close item(key, k, pub);
  //@ close item(payload, pay, pub);
}

void hmac_verify(struct item *hmac, struct item *key, struct item *payload)
  /*@ requires [?f]world(?pub) &*&
               item(hmac, ?h, pub) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*& 
               k == symmetric_key_item(?principal, ?count); @*/
  /*@ ensures  [f]world(pub) &*&
               item(hmac, h, pub) &*& 
               item(payload, pay, pub) &*& item(key, k, pub) &*&
                 collision_in_run() ? 
                   true 
                 :
                   h == hmac_item(principal, count, some(pay)); @*/
{
  check_is_symmetric_key(key);
  check_is_hmac(hmac);
  
  struct item *calc_hmac = create_hmac(key, payload);
  //@ open item(calc_hmac, ?calc_h, pub);
  //@ open item(hmac, h, pub);
  //@ open item(payload, pay, pub);
  if (hmac->size == calc_hmac->size)
  {
    if (0 == memcmp((void*) (hmac->content), (void*) (calc_hmac->content),
                    (unsigned int) hmac->size))
    {
      /*@ if (!collision_in_run())
          {
            assert calc_h == hmac_item(principal, count, some(pay));
            open [_]item_constraints(_, calc_h, ?calc_h_cs, pub);
            open [_]item_constraints_no_collision(calc_h, calc_h_cs, pub);
            open [_]item_constraints(_, h, ?h_cs, pub);
            open [_]item_constraints_no_collision(h, h_cs, pub);
            assert calc_h_cs == h_cs;
            item_constraints_injective(h_cs, h, calc_h);
            assert h == calc_h;
          }
      @*/
      //@ close item(payload, pay, pub);
      //@ close item(calc_hmac, calc_h, pub);
      //@ close item(hmac, h, pub);
      item_free(calc_hmac);
      return;
    }
  }
  
  abort_crypto_lib("Hmac to verify was not correct");
}
