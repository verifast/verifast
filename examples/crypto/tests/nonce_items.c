#include "tests.h"

void test_nonce_items()
{
  struct score *s = start_test();

  struct item *nonce1;
  struct item *nonce11;
  struct item *nonce2;
  struct item *nonce3;
  struct item *nonce4;
  struct item *nonce5;

  // Test creation of nonces
  nonce1 = create_nonce();
  nonce2 = create_nonce();
  update_test(!item_equals(nonce1, nonce2), s);
  item_free(nonce1);
  item_free(nonce2);
  
  // Test increment of nonces
  nonce1 = create_nonce();
  nonce11 = item_clone(nonce1);
  nonce2 =  item_clone(nonce1);  increment_nonce(nonce2);
  nonce3 =  item_clone(nonce2);  increment_nonce(nonce3);
  nonce4 =  item_clone(nonce1);  increment_nonce(nonce4);
  nonce5 =  item_clone(nonce11); increment_nonce(nonce5);
  update_test(!item_equals(nonce1, nonce2), s);
  update_test(!item_equals(nonce1, nonce3), s);
  update_test(!item_equals(nonce1, nonce4), s);
  update_test(!item_equals(nonce2, nonce3), s);
  update_test( item_equals(nonce2, nonce4), s);
  item_free(nonce1);
  item_free(nonce2);
  item_free(nonce3);
  item_free(nonce4);
  item_free(nonce5);
  
  finish_test("nonce items", s);
}