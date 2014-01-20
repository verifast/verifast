#include "tests.h"

void test_pair_items()
{
  struct score *s = start_test();

  struct item *item1 = create_data_item(1);
  struct item *item2 = create_data_item(2);
  struct item *item3;
  struct item *item4;
  struct item *pair1;
  struct item *pair2;
  
  // Creating a pair
  pair1 = create_pair(item1, item2);
  pair2 = create_pair(item1, item2);
  update_test(item_equals(pair1, pair2), s);
  item_free(pair2);
  pair2 = create_pair(item2, item1);
  update_test(!item_equals(pair1, pair2), s);
  item_free(pair1);
  item_free(pair2);
  
  // Destructing a pair to first
  pair1 = create_pair(item1, item2);
  item3 = pair_get_first(pair1);
  item4 = pair_get_first(pair1);
  update_test(item_equals(item1, item3), s);
  update_test(item_equals(item3, item4), s);
  item_free(pair1);
  item_free(item3);
  item_free(item4);
  
  // Destructing a pair to second
  pair1 = create_pair(item1, item2);
  item3 = pair_get_second(pair1);
  item4 = pair_get_second(pair1);
  update_test(item_equals(item2, item3), s);
  update_test(item_equals(item3, item4), s);
  item_free(pair1);
  item_free(item3);
  item_free(item4);
  
  item_free(item1);
  item_free(item2);
  
  finish_test("pair items", s);
}