#include "tests.h"

#include <unistd.h>
#include <pthread.h>

bool is_encrypted(struct item *item);
void print_item2(FILE *f, const struct item* item);

void *server(void *arg)
{
  struct score *s = (struct score *) arg;
  struct network_status *stat = network_bind(121212);
  
  struct item *data_to_send = create_data_item(10);
  network_send(stat, data_to_send);
  
  struct item *data_received = network_receive(stat);
  update_test(item_get_data(data_received) == 5, s);
  item_free(data_received);
  item_free(data_to_send);
  
  data_received = network_receive(stat);
  update_test(is_encrypted(data_received), s);
  network_send(stat, data_received);
  item_free(data_received);
  
  struct item *nonce = create_nonce();
  struct item *key = create_key();
  
  struct item *encrypted = encrypt(key, nonce);
  update_test(is_encrypted(encrypted), s);
  network_send(stat, encrypted);
  
  item_free(encrypted);
  encrypted = network_receive(stat);
  update_test(is_encrypted(encrypted), s);
  struct item *decrypted = decrypt(key, encrypted);
  update_test(!is_encrypted(decrypted), s);
  update_test(item_equals(nonce, decrypted), s);
  
  item_free(nonce);
  item_free(key);
  item_free(encrypted);
  item_free(decrypted);
  
  network_disconnect(stat);
  return NULL;
}

void *client(void *arg)
{
  struct score *s = (struct score *) arg;
  struct network_status *stat = network_connect("localhost", 121212);
  
  struct item *data_received = network_receive(stat);
  update_test(item_get_data(data_received) == 10, s);
  struct item *data_to_send = create_data_item(5);
  network_send(stat, data_to_send);
  item_free(data_received);
  item_free(data_to_send);
  
  struct item *nonce = create_nonce();
  struct item *key = create_key();
  
  struct item *encrypted = encrypt(key, nonce);
  update_test(is_encrypted(encrypted), s);
  network_send(stat, encrypted);
  item_free(encrypted);
  encrypted = network_receive(stat);
  update_test(is_encrypted(encrypted), s);
  struct item *decrypted = decrypt(key, encrypted);
  update_test(!is_encrypted(decrypted), s);
  update_test(item_equals(nonce, decrypted), s);
  item_free(nonce);
  item_free(key);
  item_free(encrypted);
  item_free(decrypted);
  
  data_received = network_receive(stat);
  update_test(is_encrypted(data_received), s);
  network_send(stat, data_received);
  item_free(data_received);

  network_disconnect(stat);
  return NULL;
}

void test_networking()
{
  struct score *s = start_test();
  struct score *s_server = start_test();
  struct score *s_client = start_test();
  
  pthread_t server_thread;
  pthread_t client_thread;
  
  /* run the server */
  if(pthread_create(&server_thread, NULL, &server, s_server)) 
     update_test(false, s);
  else
     update_test(true, s);

  /* run the client */
  if(pthread_create(&client_thread, NULL, &client, s_client)) 
     update_test(false, s);
  else
     update_test(true, s);
  
  /* wait for the server to finish */
  if(pthread_join(server_thread, NULL)) 
     update_test(false, s);
  else
     update_test(true, s);
  
  /* wait for the client to finish */
  if(pthread_join(client_thread, NULL)) 
     update_test(false, s);
  else
     update_test(true, s);

  finish_test("networking - general", s);
  finish_test("networking - client", s_client);
  finish_test("networking - server", s_server);
}
