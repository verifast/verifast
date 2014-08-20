#include "tests.h"

void test_data_items()
{
  struct score *s = start_test();

  struct item *data1;
  struct item *data2;

  // Test equality of data items
  data1 = create_data_item(1);
  data2 = data1;
  update_test(item_equals(data1, data2), s);
  update_test(item_get_data(data1) == 1, s);
  update_test(item_get_data(data2) == 1, s);
  data2 = create_data_item(1);
  update_test(item_equals(data1, data2), s);
  item_free(data1);
  item_free(data2);
  
  // Test inequality of data items
  data1 = create_data_item(2);
  data2 = create_data_item(3);
  update_test(!item_equals(data1, data2), s);
  update_test(item_get_data(data1) == 2, s);
  update_test(item_get_data(data2) == 3, s);
  item_free(data1);
  item_free(data2);
  
  finish_test("data items", s);
}