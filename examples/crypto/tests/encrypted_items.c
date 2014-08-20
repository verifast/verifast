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

  struct item *key = create_symmetric_key();
  
  result1 = encrypt(key, data);
  result2 = decrypt(key, result1);
  update_test(item_equals(data, result2), s);
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
  
  result1 = encrypt(key, pair);
  result2 = decrypt(key, result1);
  update_test(!item_equals(pair, result1), s);
  update_test(item_equals(pair, result2), s);
  item_free(result1);
  item_free(result2);
  
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

void test_asymmetric_encrypted_items()
{
  struct score *s = start_test();
  
  struct item *result1 = 0;
  struct item *result2 = 0;
  struct item *result3 = 0;
  struct item *result4 = 0;
  
  struct item *data = create_data_item(2);
  struct item *nonce = create_nonce();
  struct item *pair = create_pair(data, nonce);

  struct keypair *keypair = create_keypair(9);
  struct item *priv_key = keypair_get_private_key(keypair);
  struct item *pub_key = keypair_get_public_key(keypair);
  
  result1 = encrypt(pub_key, data);
  result2 = decrypt(priv_key, result1);
  update_test(item_equals(data, result2), s);
  item_free(result1);
  item_free(result2);
  
  result1 = encrypt(pub_key, data);
  result2 = encrypt(pub_key, data);
  update_test(!item_equals(data, result1), s);
  update_test(!item_equals(data, result2), s);
  result3 = decrypt(priv_key, result1);
  result4 = decrypt(priv_key, result2);
  update_test(item_equals(data, result3), s);
  update_test(item_equals(data, result4), s);
  item_free(result1);
  item_free(result2);
  item_free(result3);
  item_free(result4);
  
  result1 = encrypt(pub_key, pair);
  result2 = decrypt(priv_key, result1);
  update_test(!item_equals(pair, result1), s);
  update_test(item_equals(pair, result2), s);
  item_free(result1);
  item_free(result2);
  
  item_free(data);
  item_free(nonce);
  item_free(pair);
  item_free(pub_key);
  item_free(priv_key);
  finish_test("symmetric encrypted items", s);
}

void test_encrypted_items()
{
  test_symmetric_encrypted_items();
  test_asymmetric_encrypted_items();
}