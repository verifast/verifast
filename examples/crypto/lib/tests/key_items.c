#include "tests.h"

bool is_key(struct item *item);
bool is_symmetric_key(struct item *item);
bool is_public_key(struct item *item);
bool is_private_key(struct item *item);

void test_key_items()
{
  struct score *s = start_test();

  struct item *nonce = create_nonce();
  update_test(!is_key(nonce), s);
  update_test(!is_symmetric_key(nonce), s);
  item_free(nonce);
  
  struct item *key_sym = create_key();
  update_test(is_key(key_sym), s);
  update_test(is_symmetric_key(key_sym), s);
  item_free(key_sym);

  struct keypair *key_pair = create_keypair(choose());
  struct item *key_priv    = keypair_get_private_key(key_pair);
  struct item *key_pub     = keypair_get_public_key(key_pair);
  update_test(is_key(key_priv), s);
  update_test(is_private_key(key_priv), s);
  update_test(is_key(key_pub), s);
  update_test(is_public_key(key_pub), s);
  item_free(key_priv);
  item_free(key_pub);
  
  finish_test("key items", s);
}
