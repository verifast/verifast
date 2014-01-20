#include "tests.h"

void test_symmetric_encrypted_items()
{
  struct score *s = start_test();
  
  struct item *result1 = 0;
  struct item *result2 = 0;
  struct item *result3 = 0;
  struct item *result4 = 0;
  
  struct item *data = create_data_item(2);
  struct item *nonce = create_nonce();
  struct item *pair = create_pair(data, nonce);

  struct item *key = create_key();

  result1 = encrypt(key, pair);
  result2 = decrypt(key, result1);
  update_test(!item_equals(pair, result1), s);
  update_test(item_equals(pair, result2), s);
  item_free(result1);
  item_free(result2);
  
  result1 = encrypt(key, data);
  result2 = encrypt(key, data);
  update_test(!item_equals(data, result1), s);
  update_test(!item_equals(data, result2), s);
  result3 = decrypt(key, result1);
  result4 = decrypt(key, result2);
  update_test(item_equals(data, result3), s);
  update_test(item_equals(data, result4), s);
  item_free(result1);
  item_free(result2);
  item_free(result3);
  item_free(result4);
  
  result1 = encrypt(key, nonce);
  result2 = encrypt(key, result1);
  update_test(!item_equals(result1, nonce), s);
  update_test(!item_equals(result1, result2), s);
  result3 = decrypt(key, result2);
  result4 = decrypt(key, result3);
  update_test(!item_equals(result3, result2), s);
  update_test(!item_equals(result3, nonce), s);
  update_test(item_equals(result3, result1), s);
  update_test(item_equals(nonce, result4), s);
  item_free(result1);
  item_free(result2);
  item_free(result3);
  item_free(result4);
  
  item_free(data);
  item_free(nonce);
  item_free(pair);
  item_free(key);
  finish_test("symmetric encrypted items", s);
}

void test_assymmetric_encrypted_items()
{
  struct score *s = start_test();
  
  struct item *result1 = 0;
  struct item *result2 = 0;
  struct item *result3 = 0;
  struct item *result4 = 0;
  
  struct item *data = create_data_item(2);
  struct item *nonce = create_nonce();
  struct item *pair = create_pair(data, nonce);

  struct keypair *keypair = create_keypair(choose());
  struct item *priv_key = keypair_get_private_key(keypair);
  struct item *pub_key = keypair_get_public_key(keypair);
  
  struct item *enc;
  struct item *dec;
  
  // Encrypt public, decrypt private
  enc = encrypt(pub_key, data);
  update_test(!item_equals(enc, data), s);
  dec = decrypt(priv_key, enc);
  update_test(item_equals(dec, data), s);
  item_free(enc);
  item_free(dec);
  
  enc = encrypt(pub_key, nonce);
  update_test(!item_equals(enc, nonce), s);
  dec = decrypt(priv_key, enc);
  update_test(item_equals(dec, nonce), s);
  item_free(enc);
  item_free(dec);
  
  enc = encrypt(pub_key, pair);
  update_test(!item_equals(enc, pair), s);
  dec = decrypt(priv_key, enc);
  update_test(item_equals(dec, pair), s);
  item_free(enc);
  item_free(dec);

  item_free(data);
  item_free(nonce);
  item_free(pair);
  item_free(priv_key);
  item_free(pub_key);
  
  finish_test("assymmetric encrypted items", s);
}

void test_encrypted_items()
{
  test_symmetric_encrypted_items();
  test_assymmetric_encrypted_items();
}