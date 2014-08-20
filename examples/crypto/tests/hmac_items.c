#include "tests.h"

void test_hmac_items()
{
  struct score *s = start_test();
  
  struct item *result1 = 0;
  struct item *result2 = 0;
  
  struct item *data = create_data_item(2);
  struct item *nonce = create_nonce();
  struct item *pair = create_pair(data, nonce);

  struct item *key = create_symmetric_key();

  result1 = hmac(key, data);
  result2 = hmac(key, data);
  update_test(item_equals(result1, result2), s);
  item_free(result1);
  item_free(result2);
  
  result1 = hmac(key, nonce);
  result2 = hmac(key, nonce);
  update_test(item_equals(result1, result2), s);
  item_free(result1);
  item_free(result2);
  
  result1 = hmac(key, pair);
  result2 = hmac(key, pair);
  update_test(item_equals(result1, result2), s);
  item_free(result1);
  item_free(result2);
  
  result1 = hmac(key, data);
  result2 = hmac(key, nonce);
  update_test(!item_equals(result1, result2), s);
  item_free(result1);
  item_free(result2);
  
  result1 = hmac(key, data);
  result2 = hmac(key, pair);
  update_test(!item_equals(result1, result2), s);
  item_free(result1);
  item_free(result2);
  
  result1 = hmac(key, nonce);
  result2 = hmac(key, pair);
  update_test(!item_equals(result1, result2), s);
  item_free(result1);
  item_free(result2);
  
  item_free(data);
  item_free(nonce);
  item_free(pair);
  item_free(key);

  finish_test("hmac items", s);
}