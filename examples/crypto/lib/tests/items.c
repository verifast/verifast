#include "tests.h"

struct item *item_create(int i);
struct item* item_create_initialized(int tag, unsigned char* buffer, size_t size);
struct item *item_clone(struct item * item);

size_t item_serialize(unsigned char** dest, struct item* item);
struct item* item_deserialize(unsigned char* buffer);

void test_items()
{
  struct score *s = start_test();

  int size, content;
  struct item *item1;
  struct item *item2;

  // Test equality of items
  item1 = item_create(0);
  item2 = item1;
  update_test(item_equals(item1, item2), s);
  item_free(item1);
  
  item1 = item_create(1);
  item2 = item_clone(item1);
  update_test(item_equals(item1, item2), s);
  item_free(item1);
  item_free(item2);
  
  size = sizeof(int);
  content = 123;
  item1 = item_create_initialized(2, (unsigned char*) &content, size);
  item2 = item_create_initialized(2, (unsigned char*) &content, size);
  update_test(item_equals(item1, item2), s);
  item_free(item1);
  item_free(item2);
  
  // Test inequality of items
  item1 = item_create(3);
  item2 = item_create(4);
  update_test(!item_equals(item1, item2), s);
  item_free(item1);
  item_free(item2);
  
  size = sizeof(int);
  content = 456;
  item1 = item_create_initialized(1, (unsigned char*) &content, size);
  content = 789;
  item2 = item_create_initialized(1, (unsigned char*) &content, size);
  update_test(!item_equals(item1, item2), s);
  item_free(item1);
  item_free(item2);
  
  size = sizeof(int);
  content = 123;
  item1 = item_create_initialized(1, (unsigned char*) &content, size);
  size = sizeof(int) - 1;
  item2 = item_create_initialized(1, (unsigned char*) &content, size);
  update_test(!item_equals(item1, item2), s);
  item_free(item1);
  item_free(item2);
  
  // Test serialization/deserialization of items
  size = sizeof(int);
  content = 123;
  item1 = item_create_initialized(5, (unsigned char*) &content, size);
  unsigned char* buffer = 0;
  item_serialize(&buffer, item1);
  item2 = item_deserialize(buffer);
  update_test(item_equals(item1, item2), s);
  item_free(item2);
  *((int*) (buffer + sizeof(int) + sizeof(size_t))) = 321;
  item2 = item_deserialize(buffer);
  update_test(!item_equals(item1, item2), s);
  item_free(item2);
  *((int*) (buffer + sizeof(int) + sizeof(size_t))) = 123;
  item2 = item_deserialize(buffer);
  update_test(item_equals(item1, item2), s);
  item_free(item1);
  item_free(item2);
  free(buffer);  

  finish_test("general items", s);
}
