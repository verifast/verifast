#include "tests.h"

bool is_key(struct item *item);

void test_key_items()
{
  struct score *s = start_test();

  struct item *nonce = create_nonce();
  update_test(!is_key(nonce), s);
  item_free(nonce);
  
  struct item *key = create_symmetric_key();
  update_test(is_key(key), s);
  item_free(key);
  
  struct keypair *pair = create_keypair(9);
  struct item *priv_key = keypair_get_private_key(pair);
  update_test(is_key(key), s);
  struct item *pub_key = keypair_get_public_key(pair);
  update_test(is_key(key), s);
  item_free(pub_key);
  item_free(priv_key);
  
  finish_test("key items", s);
}
