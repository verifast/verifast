#include "tests.h"

struct score
{
  int result;
  int total;
  
  int failing_test;
};

struct score* start_test()
{
  struct score *s = malloc(sizeof(struct score));
  s->result = 0;
  s->total = 0;
  return s;
}

void update_test(bool result, struct score *s)
{
  s->total++;
  
  if (result) 
    s->result++;
  else
    s->failing_test = s->total;
}

void finish_test(char* name, struct score *s)
{
  printf(">>> Test %s: \n\t%i/%i\n", name, s->result, s->total);
  
  if (s->result != s->total) 
  {
    printf(">>>\n");
    printf(">>> \tTest %i failed!!!\n", s->failing_test);
    printf(">>>\n");
    free(s);
    abort();
  }
  free(s);
}

void print_welcome()
{
  printf("\t---------------------------------------\n");
  printf("\tTesting dolevyoa library implementation\n");
  printf("\t---------------------------------------\n");
}

void print_goodbye()
{
  printf("\t---------------------------------------\n");
  printf("\tTests finished successfully,   Goodbye!\n");
  printf("\t---------------------------------------\n");
}

int main()
{
  print_welcome();
  init_crypto_lib();

  test_nonce_items();
  test_key_items();
  test_data_items();
  test_hmac_items();  
  test_pair_items();
  test_encrypted_items();
  test_networking();

  print_goodbye();
  return 0;
}
