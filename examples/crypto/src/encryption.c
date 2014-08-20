#include "encryption.h"

#include "item.h"
#include "key_item.h"
#include "principals.h"
#include "symmetric_encryption.h"
#include "asymmetric_encryption.h"

struct item *encrypt(struct item *key, struct item *payload)
  /*@ requires [?f]world(?pub) &*&
               item(key, ?key_i) &*& 
               key_i == key_item(?s, ?count1, ?kind, ?info) &*&
               item(payload, ?pay_i) &*&
               generated_values(?principal, ?count2);
  @*/
  /*@ ensures  [f]world(pub) &*&
               item(key, key_item(s, count1, kind, info)) &*&
               item(payload, pay_i) &*&
               generated_values(principal, count2 + 1) &*&
               item(result, encrypted_item(?key_enc, ?pay_enc, ?entropy)) &*&
               true == if_no_collision(key_enc == key_i && pay_enc == pay_i);
  @*/
{
  struct item *result = 0;
  
  check_is_key(key);
  //@ open item(key, key_i);
  //@ assert key->content |-> ?cont &*& key->size |-> ?size;
  //@ open chars(cont, size, ?cs);
  char kkind = *(key->content);
  //@ close chars(cont, size, cs);
  //@ close item(key, key_i);
  
  /*@
      switch (kind)
      {
        case symmetric_key:
          assert true;
        case public_key:
          assert true;
        case private_key:
          assert true;
      }
  @*/
  /*@ 
      if (kkind == 'a')
      {
        open  item(key, key_i);
        close item(key, key_item(s, count1, symmetric_key, info));
      }
      else if (kkind == 'b')
      {
        open  item(key, key_i);
        close item(key, key_item(s, count1, public_key, info));
      }
      else
      {
        open  item(key, key_i);
        close item(key, key_item(s, count1, private_key, info));
      }
  @*/
      
  switch(kkind)
  {
    case 'a':
      result = sym_encrypt(key, payload);
      break;
    case 'b':
      result = asym_encrypt(key, payload);
      break;
    default:
      abort_crypto_lib("Invalid key for encryption");
  }
  
  /*@ 
      if (kkind == 'a')
      {
        open  item(key, key_item(s, count1, symmetric_key, info));
        close item(key, key_i);
      }
      else if (kkind == 'b')
      {
        open  item(key, key_item(s, count1, public_key, info));
        close item(key, key_i);
      }
      else
      {
        open  item(key, key_item(s, count1, private_key, info));
        close item(key, key_i);
      }
  @*/
  
  return result;
}

struct item *decrypt(struct item *key, struct item *item)
  /*@ requires [?f]world(?pub) &*& item(item, ?i) &*&
               item(key, ?key_i) &*&
               key_i == key_item(?participant, ?count, ?kind, ?info) &*&
               generated_values(?principal, ?count2);
  @*/
  /*@ ensures  [f]world(pub) &*& item(item, i) &*&
               item(key, key_i) &*&
               generated_values(principal, ?count3) &*& count3 >= count2 &*&
               switch (i)
               {
                 case nonce_item(p0, c0, inc0, i0): return false;
                 case key_item(p0, c0, k0, i0): return false;
                 case data_item(d0): return false;
                 case hmac_item(k0, payload0): return false;
                 case encrypted_item(key0, pay0, ent0): return
                     item(result, ?resulti) &*&
                     true == if_no_collision(
                       resulti == pay0 && 
                       key0 == key_item(participant, count, 
                                        inverse_key_kind(kind), info) 
                     );
                 case pair_item(f0, s0): return false;
               };
  @*/
{
  struct item *result = 0;
  
  check_is_key(key);
  //@ open item(key, key_i);
  //@ assert key->content |-> ?cont &*& key->size |-> ?size;
  //@ open chars(cont, size, ?cs);
  char kkind = *(key->content);
  //@ close chars(cont, size, cs);
  //@ close item(key, key_i);
  
  /*@
      switch (kind)
      {
        case symmetric_key:
          assert true;
        case public_key:
          assert true;
        case private_key:
          assert true;
      }
  @*/
  /*@ 
      if (kkind == 'a')
      {
        open  item(key, key_i);
        close item(key, key_item(participant, count, symmetric_key, info));
      }
      else if (kkind == 'b')
      {
        open  item(key, key_i);
        close item(key, key_item(participant, count, public_key, info));
      }
      else
      {
        open  item(key, key_i);
        close item(key, key_item(participant, count, private_key, info));
      }
  @*/
      
  switch(kkind)
  {
    case 'a':
      result = sym_decrypt(key, item);
      break;
    case 'c':
      result = asym_decrypt(key, item);
      break;
    default:
      abort_crypto_lib("Invalid key for decryption");
  }
  
  /*@ 
      if (kkind == 'a')
      {
        open  item(key, key_item(participant, count, symmetric_key, info));
        close item(key, key_i);
      }
      else if (kkind == 'b')
      {
        open  item(key, key_item(participant, count, public_key, info));
        close item(key, key_i);
      }
      else
      {
        open  item(key, key_item(participant, count, private_key, info));
        close item(key, key_i);
      }
  @*/
  
  return result;
}
