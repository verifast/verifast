#include "tests.h"

#include <unistd.h>
#include <pthread.h>

bool is_hmac(struct item *item);
//void print_item2(FILE *f, const struct item* item);

void *server(void *arg)
{
  struct score *s = (struct score *) arg;
  struct network_status *stat = network_bind_and_accept(121212);
  
  struct item *data_to_send = create_data_item(10);
  network_send(stat, data_to_send);
  
  struct item *data_received = network_receive(stat);
  update_test(item_get_data(data_received) == 5, s);
  item_free(data_received);
  item_free(data_to_send);
  
  data_received = network_receive(stat);
  update_test(is_hmac(data_received), s);
  network_send(stat, data_received);
  item_free(data_received);
  
  struct item *nonce = create_nonce();
  struct item *key = create_symmetric_key();
  
  struct item *hmaci = hmac(key, nonce);
  update_test(is_hmac(hmaci), s);
  network_send(stat, hmaci);
  
  item_free(hmaci);
  hmaci = network_receive(stat);
  update_test(is_hmac(hmaci), s);
  
  hmac_verify(hmaci, key, nonce);
  
  item_free(nonce);
  item_free(key);
  item_free(hmaci);
  
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
  struct item *key = create_symmetric_key();
  
  struct item *hmaci = hmac(key, nonce);
  update_test(is_hmac(hmaci), s);
  network_send(stat, hmaci);
  item_free(hmaci);
  hmaci = network_receive(stat);
  update_test(is_hmac(hmaci), s);
  
  hmac_verify(hmaci, key, nonce);
  
  item_free(nonce);
  item_free(key);
  item_free(hmaci);
  
  data_received = network_receive(stat);
  update_test(is_hmac(data_received), s);
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
