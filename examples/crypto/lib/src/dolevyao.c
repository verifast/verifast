#include "dolevyao.h"

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <math.h>

#include "polarssl/net.h"
#include "polarssl/aes.h"
#include "polarssl/rsa.h"
#include "polarssl/havege.h"
#include "polarssl/sha512.h"

#define PRIM_BIT_SIZE    1024
#define PRIM_BYTE_SIZE   (PRIM_BIT_SIZE / 8)
#define MAX_PACKAGE_SIZE 1024 * 8

///////////////////////////////////////////////////////////////////////////////
// Item definition ////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item
{
  // 0 = nonce_item
  // 1 = key_item
  // 2 = data_item
  // 3 = hmac_item
  // 4 = encrypted_item
  // 5 = pair_item
  int tag;
  
  size_t size;
  unsigned char* content;
};

///////////////////////////////////////////////////////////////////////////////
// Debugging //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

#define BIT64

#ifdef DEBUG
int indent;
#endif

void debug_print(const char *message)
{
#ifdef DEBUG
  printf("<DEBUG>%s\n", message);
#endif
}

void print_buffer(const unsigned char *buffer, size_t size)
{
#ifdef DEBUG
  for (int i = 0; i < size; i++)
  {
    if (i % 32 == 0)
      printf("\n");
    
    printf("%02X", buffer[i]);
  }
  printf("\n");
#endif
}

void print_item(const struct item* item)
{
#ifdef DEBUG
  printf("---------------------\n");
  printf("Item: %p\n", item);
  printf("\ttag %i\n", item->tag);
  
#ifdef BIT64
  printf("\tsize %lu\n", item->size);
#else
  printf("\tsize %u\n", item->size);
#endif
  
  printf("\tcontent:");
  print_buffer(item->content, item->size);
  printf("---------------------\n");
#endif
}

///////////////////////////////////////////////////////////////////////////////
// Initialization /////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

havege_state random_state;

void init_crypto_lib()
{
  havege_init(&random_state);
#ifdef DEBUG
  indent = 0;
#endif
}

///////////////////////////////////////////////////////////////////////////////
// General definitions ////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void abort_crypto_lib(const char* message)
{
  printf("An error has occurred while using the crypto library:\n"
         "\n\t%s\n\nAborting...\n", message);
  abort();
}

void *malloc_wrapper(size_t size)
{
  if (size > MAX_PACKAGE_SIZE)
    abort_crypto_lib("requested humongous malloc!!!!!!!!");
    
  void* result = 0;
  if ((result = malloc(size)) == 0)
    abort_crypto_lib("Malloc failed");

  return result;
}


void random_buffer(unsigned char* buffer, size_t size)
{
  havege_random(&random_state, buffer, size);
}

void write_buffer(unsigned char **target, const unsigned char *source, 
                  size_t length)
{
  memcpy(*target, source, length);
  *target += length;
}

int random_int()
{
  int rand;
  random_buffer((unsigned char*) &rand, sizeof(int));

  return rand;
}

int choose()
{
  return random_int();
}

///////////////////////////////////////////////////////////////////////////////
// Item manipulation/inspection ///////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool item_equals(struct item *item1, struct item *item2)
{ 
  debug_print("COMPARING ITEMS\n");
  print_item(item1);
  print_item(item2);
  
  bool result = false;
  
  if (item1 != item2)
  {
    result = false;
    
    if (item1->tag == item2->tag && item1->size == item2->size)
    {
      if (memcmp(item1->content, item2->content, item1->size) == 0)
      {
#ifdef DEBUG
        debug_print("\tFound different, but identical items");
#endif
        result = true;
      }
    }
  }
  else
  {
    result = true; 
  }
  
  return result;
}

struct item* item_create(int tag)
{
  struct item* item = malloc_wrapper(sizeof(struct item));
  
  item->tag = tag;
  item->size = 0;
  item->content = 0;

  return item;
}

struct item* item_create_initialized(int tag, unsigned char* buffer, 
                                     size_t size)
{
  struct item* item = item_create(tag);

  item->size = size;
  item->content = malloc_wrapper(size);
  memcpy(item->content, buffer, size);

  return item;
}

struct item* item_clone(struct item* item)
{
  struct item* result =
                item_create_initialized(item->tag, item->content, item->size);

  return result;
}

void item_free(struct item* item)
{
  if (item->content!=0)
    free(item->content);
    
  free(item);  
}

size_t item_serialize(unsigned char** dest, struct item* item)
{
  size_t size = sizeof(int) + sizeof(size_t) + item->size;
  *dest = malloc_wrapper(size);
  
  unsigned char *buffer = *dest;
  write_buffer(&buffer, (unsigned char*) &(item->tag),  sizeof(int));
  write_buffer(&buffer, (unsigned char*) &(item->size), sizeof(size_t));
  write_buffer(&buffer, (unsigned char*) item->content, item->size);

  return size;
}

struct item* item_deserialize(unsigned char* buffer)
{
  int tag = *((int*) buffer);
  buffer += sizeof(int);
  size_t size = *((size_t*) buffer);
  buffer += sizeof(size_t);

  struct item *result = item_create_initialized(tag, buffer, size);

  return result;
}

///////////////////////////////////////////////////////////////////////////////
// Nonce item /////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *create_nonce()
{
  unsigned char* buffer = malloc_wrapper(PRIM_BYTE_SIZE);
  random_buffer(buffer, PRIM_BYTE_SIZE);
  
  struct item* nonce = item_create_initialized(0, buffer, PRIM_BYTE_SIZE);
  free(buffer);

  return nonce;
}

bool is_nonce(struct item *item)
{
  return (item->tag == 0);
}

void check_is_nonce(struct item *item)
{
  if (!is_nonce(item))
    abort_crypto_lib("Presented item is not a nonce");
}

struct item *increment_nonce(struct item *item, int amount)
{
  debug_print("incrementing nonce");
  print_item(item);
  
  check_is_nonce(item);
    
  struct item* inc = item_clone(item);
  
  *(inc->content) += amount;

  print_item(inc);
  
  return inc;
}

///////////////////////////////////////////////////////////////////////////////
// Key item ///////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

// extra int in content to indicate key kind:
//    0 -> symmetric_key
//    1 -> public_key
//    2 -> private_key

struct item *create_key_core(int label, const unsigned char *buffer, 
                             size_t length)
{
  size_t total_size = sizeof(int) + length;
  
  unsigned char* total_buffer = malloc_wrapper(total_size);
  unsigned char* temp = total_buffer;
  
  write_buffer(&temp, (unsigned char*) &(label), sizeof(int));
  write_buffer(&temp, buffer, length);

  struct item* key = item_create_initialized(1, total_buffer, total_size);
  free(total_buffer);

  return key;
}

struct item *create_key()
{
  unsigned char* buffer = malloc_wrapper(PRIM_BYTE_SIZE);
  random_buffer(buffer, PRIM_BYTE_SIZE);
  struct item *result = create_key_core(0, buffer, PRIM_BYTE_SIZE);
  free(buffer);

  return result;
}

struct item *key_clone(struct item *key)
{
  return item_clone(key);
}

size_t get_key_length(struct item *key)
{
  return key->size - sizeof(int);
}

unsigned char *get_key_value(struct item *key)
{
  size_t key_length = get_key_length(key);
  unsigned char *result = malloc_wrapper(key_length);
  memcpy(result, key->content + sizeof(int), key_length);

  return result;
}

void key_free(struct item* key)
{
  item_free(key);
}

bool is_key(struct item *item)
{
  return item->tag == 1;
}

bool is_symmetric_key(struct item *item)
{
  return *((int*) item->content) == 0;
}

bool is_public_key(struct item *item)
{
  return *((int*) item->content) == 1;
}

void check_is_public_key(struct item *item)
{
  if (!is_public_key(item))
    abort_crypto_lib("Presented item is not a public key");
}

bool is_private_key(struct item *item)
{
  return *((int*) item->content) == 2;
}

void check_is_private_key(struct item *item)
{
  if (!is_private_key(item))
    abort_crypto_lib("Presented item is not a private key");
}

void check_is_key(struct item *item)
{
  if (!is_key(item))
    abort_crypto_lib("Presented item is not a key item");
}
 
struct keypair
{
  struct item *public_key;
  struct item *private_key;
};

struct item *create_public_key(const rsa_context* context)
{
  size_t length_N = context->N.n * (sizeof(*(context->N.p)));
  unsigned char*  value_N  = malloc_wrapper(length_N);
  size_t length_E = context->E.n * (sizeof(*(context->E.p)));
  unsigned char*  value_E  = malloc_wrapper(length_E);

  if ((mpi_write_binary(&context->N, value_N, length_N) != 0) ||
      (mpi_write_binary(&context->E, value_E, length_E) != 0) )
  {
    abort_crypto_lib("Could not serialize public key components");
  }

  size_t total_size = 3 * sizeof(size_t) + length_N + length_E;
  unsigned char* total_buffer = malloc_wrapper(total_size);
  unsigned char* buffer = total_buffer;

  write_buffer(&buffer, (unsigned char*) &context->len, sizeof(size_t));
  write_buffer(&buffer, (unsigned char*) &length_N, sizeof(size_t));
  write_buffer(&buffer, (unsigned char*) value_N, length_N);
  write_buffer(&buffer, (unsigned char*) &length_E, sizeof(size_t));
  write_buffer(&buffer, (unsigned char*) value_E, length_E);

  struct item* key = create_key_core(1, total_buffer, total_size);
  
  free(value_N);
  free(value_E);
  free(total_buffer);

  return key;
}

void retreive_public_key(rsa_context* context, struct item *key)
{
  check_is_public_key(key);

  unsigned char *key_value = get_key_value(key);
  unsigned char *buffer = key_value;
  
  context->len = *((size_t *) buffer);
    buffer += sizeof(size_t);
  size_t length_N = *((size_t *) buffer);
    buffer += sizeof(size_t);
  unsigned char* value_N = buffer;
    buffer += length_N;
  size_t length_E = *((size_t *) buffer);
    buffer += sizeof(size_t);
  unsigned char* value_E = buffer;

  if ((mpi_read_binary(&context->N, value_N, length_N) != 0) ||
      (mpi_read_binary(&context->E, value_E, length_E) != 0) )
  {
    abort_crypto_lib("Could not deserialize public key components");
  }

  free(key_value);
}

struct item *create_private_key(const rsa_context* context)
{
  size_t length_N = context->N.n *  (sizeof(*(context->N.p)));
  unsigned char*  value_N  = malloc_wrapper(length_N);
  size_t length_E = context->E.n *  (sizeof(*(context->E.p)));
  unsigned char*  value_E  = malloc_wrapper(length_E);
  size_t length_D = context->D.n *  (sizeof(*(context->D.p)));
  unsigned char*  value_D  = malloc_wrapper(length_D);
  size_t length_P = context->P.n *  (sizeof(*(context->P.p)));
  unsigned char*  value_P  = malloc_wrapper(length_P);
  size_t length_Q = context->Q.n *  (sizeof(*(context->Q.p)));
  unsigned char*  value_Q  = malloc_wrapper(length_Q);
  size_t length_DP = context->DP.n * (sizeof(*(context->DP.p)));
  unsigned char*  value_DP = malloc_wrapper(length_DP);
  size_t length_DQ = context->DQ.n * (sizeof(*(context->DQ.p)));
  unsigned char*  value_DQ = malloc_wrapper(length_DQ);
  size_t length_QP = context->QP.n * (sizeof(*(context->QP.p)));
  unsigned char*  value_QP = malloc_wrapper(length_QP);
  
  if ((mpi_write_binary(&context->N,  value_N,  length_N)  != 0) ||
      (mpi_write_binary(&context->E,  value_E,  length_E)  != 0) ||
      (mpi_write_binary(&context->D,  value_D,  length_D)  != 0) ||
      (mpi_write_binary(&context->P,  value_P,  length_P)  != 0) ||
      (mpi_write_binary(&context->Q,  value_Q,  length_Q)  != 0) ||
      (mpi_write_binary(&context->DP, value_DP, length_DP) != 0) ||
      (mpi_write_binary(&context->DQ, value_DQ, length_DQ) != 0) ||
      (mpi_write_binary(&context->QP, value_QP, length_QP) != 0) )
  {
    abort_crypto_lib("Could not serialize private key components");
  }

  size_t total_size = 9 * sizeof(size_t) + length_N + length_E + length_D + 
                    length_P + length_Q + length_DP + length_DQ + length_QP;
  unsigned char* total_buffer = malloc_wrapper(total_size);
  unsigned char* buffer = total_buffer;

  write_buffer(&buffer, (unsigned char*) &context->len, sizeof(size_t));
  write_buffer(&buffer, (unsigned char*) &length_N, sizeof(size_t));
  write_buffer(&buffer, (unsigned char*) value_N, length_N);
  write_buffer(&buffer, (unsigned char*) &length_E, sizeof(size_t));
  write_buffer(&buffer, (unsigned char*) value_E, length_E);
  write_buffer(&buffer, (unsigned char*) &length_D, sizeof(size_t));
  write_buffer(&buffer, (unsigned char*) value_D, length_D);
  write_buffer(&buffer, (unsigned char*) &length_P, sizeof(size_t));
  write_buffer(&buffer, (unsigned char*) value_P, length_P);
  write_buffer(&buffer, (unsigned char*) &length_Q, sizeof(size_t));
  write_buffer(&buffer, (unsigned char*) value_Q, length_Q);
  write_buffer(&buffer, (unsigned char*) &length_DP, sizeof(size_t));
  write_buffer(&buffer, (unsigned char*) value_DP, length_DP);
  write_buffer(&buffer, (unsigned char*) &length_DQ, sizeof(size_t));
  write_buffer(&buffer, (unsigned char*) value_DQ, length_DQ);
  write_buffer(&buffer, (unsigned char*) &length_QP, sizeof(size_t));
  write_buffer(&buffer, (unsigned char*) value_QP, length_QP);

  struct item* key = create_key_core(2, total_buffer, total_size);
  
  free(value_N);
  free(value_E);
  free(value_D);
  free(value_P);
  free(value_Q);
  free(value_DP);
  free(value_DQ);
  free(value_QP);
  free(total_buffer);

  return key;
}

void retreive_private_key(rsa_context* context, struct item *key)
{
  check_is_private_key(key);

  unsigned char *key_value = get_key_value(key);
  unsigned char *buffer = key_value;
  
  context->len = *((size_t *) buffer);
    buffer += sizeof(size_t);
  size_t length_N = *((size_t *) buffer);
    buffer += sizeof(size_t);
  unsigned char* value_N = buffer;
    buffer += length_N;
  size_t length_E = *((size_t *) buffer);
    buffer += sizeof(size_t);
  unsigned char* value_E = buffer;
    buffer += length_E;
  size_t length_D = *((size_t *) buffer);
    buffer += sizeof(size_t);
  unsigned char* value_D = buffer;
    buffer += length_D;
  size_t length_P = *((size_t *) buffer);
    buffer += sizeof(size_t);
  unsigned char* value_P = buffer;
    buffer += length_P;
  size_t length_Q = *((size_t *) buffer);
    buffer += sizeof(size_t);
  unsigned char* value_Q = buffer;
    buffer += length_Q;
  size_t length_DP = *((size_t *) buffer);
    buffer += sizeof(size_t);
  unsigned char* value_DP = buffer;
    buffer += length_DP;
  size_t length_DQ = *((size_t *) buffer);
    buffer += sizeof(size_t);
  unsigned char* value_DQ = buffer;
    buffer += length_DQ;
  size_t length_QP = *((size_t *) buffer);
    buffer += sizeof(size_t);
  unsigned char* value_QP = buffer;

  if ((mpi_read_binary(&context->N,  value_N,  length_N)  != 0) ||
      (mpi_read_binary(&context->E,  value_E,  length_E)  != 0) ||
      (mpi_read_binary(&context->D,  value_D,  length_D)  != 0) ||
      (mpi_read_binary(&context->P,  value_P,  length_P)  != 0) ||
      (mpi_read_binary(&context->Q,  value_Q,  length_Q)  != 0) ||
      (mpi_read_binary(&context->DP, value_DP, length_DP) != 0) ||
      (mpi_read_binary(&context->DQ, value_DQ, length_DQ) != 0) ||
      (mpi_read_binary(&context->QP, value_QP, length_QP) != 0) )
  {
    abort_crypto_lib("Could not deserialize private key components");
  }

  free(key_value);
}

struct key_registry
{
  int participant;
  struct item* pub_key;
  struct key_registry* next;
};

struct key_registry *registered_keys = 0;

void register_public_key(int participant, struct item *key)
{
  struct key_registry *kr = malloc(sizeof(struct key_registry));
  
  kr->participant = participant;
  kr->pub_key = item_clone(key);
  kr->next = registered_keys;
  
  registered_keys = kr;
}

struct item *get_public_key(int participant)
{
  struct key_registry *current = registered_keys;
  
  while(current != 0)
  {
    if (current->participant == participant)
    {
      return item_clone(current->pub_key);
    }
    current = current->next;
  }
  
  abort_crypto_lib("Requested public key not found");
  return 0;
}

struct keypair *create_keypair(int principal)
{
  struct keypair *pair = malloc_wrapper(sizeof(struct keypair));
  
  rsa_context context;
  rsa_init(&context, RSA_PKCS_V15, 0); 
  
  if (rsa_gen_key(&context, &havege_random, &random_state, 
                  PRIM_BIT_SIZE, 65537) != 0)
    abort_crypto_lib("Could not generate a valid key pair");
  
  if (rsa_check_pubkey(&context) != 0)
    abort_crypto_lib("Not a valid public key");
  if (rsa_check_privkey(&context) != 0)
    abort_crypto_lib("Not a valid private key");
  
  pair->public_key = create_public_key(&context);
  pair->private_key = create_private_key(&context);

  register_public_key(principal, pair->public_key);
  
  rsa_free(&context);

  return pair;
}

void keypair_free(struct keypair *keypair)
{
  item_free(keypair->private_key);
  item_free(keypair->public_key);
  free(keypair);
}

struct item *keypair_get_private_key(struct keypair *keypair)
{
  return item_clone(keypair->private_key);
}

struct item *keypair_get_public_key(struct keypair *keypair)
{
  struct item *key_pub = item_clone(keypair->public_key);
  keypair_free(keypair);
  
  return key_pub;
}

///////////////////////////////////////////////////////////////////////////////
// Data item //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *create_data_item(int data)
{
  struct item *result = 
              item_create_initialized(2, (unsigned char*) &data, sizeof(int));

  return result;
}

bool is_data(struct item *item)
{
  return item->tag == 2;
}

void check_is_data(struct item *item)
{
  if (!is_data(item))
    abort_crypto_lib("Presented item is not a data item");
}

int item_get_data(struct item *item)
{
  check_is_data(item);

  return *((int*) item->content);
}

///////////////////////////////////////////////////////////////////////////////
// Hmac item //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *hmac(struct item *key, struct item *payload)
{
  int size = 64 * sizeof(unsigned char);
  unsigned char* output = malloc_wrapper(size);
  
  unsigned char* key_value = get_key_value(key);
  size_t key_length = get_key_length(key);
  
  sha512_hmac(key_value, key_length, payload->content, 
              payload->size, output, 0);

  struct item *result = item_create_initialized(3, output, size);

  free(output);
  free(key_value);

  return result;
}

bool hmac_is_correct(struct item *hash, struct item *key, 
                                            struct item *payload)
{
  check_is_hmac(hash);

  struct item *correct_hash = hmac(key, payload);
  bool result = item_equals(hash, correct_hash);
  free(correct_hash);

  return result;
}

void hmac_verify(struct item *hash, struct item *key, struct item *payload)
{   
  if(!hmac_is_correct(hash, key, payload))
  {
    abort_crypto_lib("Calculated hash is different from expected one");
  }
}

bool is_hmac(struct item *item)
{
  return item->tag == 3;
}

void check_is_hmac(struct item *item)
{
  if (!is_hmac(item))
    abort_crypto_lib("Presented item is not a hmac item");
}

///////////////////////////////////////////////////////////////////////////////
// Encrypted item /////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_encrypted(struct item *item)
{
  return item->tag == 4;
}

void check_is_encrypted(struct item *item)
{
  if (!is_encrypted(item))
    abort_crypto_lib("Presented item is not an encrypted item");
}

#define ENCRYPT 0
#define DECRYPT 1

size_t get_input(int mode, unsigned char **input, struct item *item)
{
  if (mode == ENCRYPT)
  {
    return item_serialize(input, item);
  }
  else if (mode == DECRYPT)
  {
    *input = malloc(item->size);
    memcpy(*input, item->content, item->size);
    return item->size;
  }
  
  abort_crypto_lib("Invalid mode for crypt operation");
  return 0;
}

struct item *get_output(int mode, unsigned char *output, size_t output_size)
{
  if (mode == ENCRYPT)
  {
    return item_create_initialized(4, output, output_size);
  }
  else if (mode == DECRYPT)
  {
    return item_deserialize(output);
  }
  
  abort_crypto_lib("Invalid mode for crypt operation");
  return 0;
}

size_t crypt_core(unsigned char **output, int mode, struct item* key,
                  unsigned char *input, size_t input_size)
{
  debug_print("begin crypt_core");
  print_buffer(input, input_size);
  
  if (mode != ENCRYPT && mode != DECRYPT) 
    abort_crypto_lib("Invalid mode for crypt operation");

  check_is_key(key);
  size_t key_size = get_key_length(key);
  unsigned char *key_value = get_key_value(key);

  size_t output_size = 0;
  if (is_symmetric_key(key))
  {
    aes_context aes;
    if (aes_setkey_enc(&aes, key_value, key_size) != 0)
      abort_crypto_lib("Invalid key provided for symmetric encryption");
    
    unsigned char iv[16];
    size_t iv_offset = 0;
    size_t iv_length = 16 * sizeof(unsigned char); 
    
    if (mode == ENCRYPT)
    {
      random_buffer(iv, iv_length);

      output_size = input_size + sizeof(size_t) + iv_length;
      *output = malloc_wrapper(output_size);
      
      unsigned char *buffer = *output;
      memcpy(buffer, &iv_offset, sizeof(size_t));
      buffer += sizeof(size_t);
      memcpy(buffer, iv, iv_length);
      buffer += iv_length;
      
      unsigned char *encrypted = malloc_wrapper(input_size);
      
      if (aes_crypt_cfb128(&aes, AES_ENCRYPT, input_size, &iv_offset, 
                          iv, input, encrypted) != 0)
        abort_crypto_lib("Encryption failed");
      
      memcpy(buffer, encrypted, input_size);
      free(encrypted);
    }
    else
    {
      unsigned char *temp = input;
      size_t iv_offset = *((size_t*) temp);
      temp += sizeof(size_t);

      memcpy(iv, temp, iv_length);
      temp += iv_length;

      unsigned char *input = temp;
      output_size = input_size - sizeof(size_t) - iv_length;
      *output = malloc_wrapper(output_size);

      if (aes_crypt_cfb128(&aes, AES_DECRYPT, output_size, &iv_offset, 
                          iv, input, *output) != 0)
        abort_crypto_lib("Decryptoin failed");
    }
  }
  else if (is_public_key(key) || is_private_key(key))
  {
    rsa_context context;
    rsa_init(&context, RSA_PKCS_V15, 0);
    
    if (is_public_key(key))
    {
      retreive_public_key(&context, key);
      if (rsa_check_pubkey(&context) != 0)
        abort_crypto_lib("Not a valid public key");
    }
    else
    {
      retreive_private_key(&context, key);
      if (rsa_check_privkey(&context) != 0)
        abort_crypto_lib("Not a valid private key");
    }
    
    size_t in_part_size = (context.len * sizeof(char));
    size_t out_part_size = in_part_size;
    if (mode == ENCRYPT) in_part_size /= 2;
    if (mode == DECRYPT) out_part_size /= 2;
    int nb_parts = 1 + ((input_size - 1) / in_part_size);
    output_size = nb_parts * out_part_size;
    *output = malloc_wrapper(output_size);
    unsigned char *current = *output;

    if (mode == ENCRYPT)
    {
      while(nb_parts-- > 0)
      {
        size_t size = input_size > in_part_size ? in_part_size : input_size;
        if (rsa_pkcs1_encrypt(&context, havege_random, &random_state, 
                                    RSA_PUBLIC, size, input, current) != 0)
          abort_crypto_lib("Encryption failed");
        input_size -= in_part_size;
        input += in_part_size;
        current += out_part_size;
      }
    }
    else
    {
      size_t temp_output_size = 0;
      while(nb_parts-- > 0)
      {
        if (rsa_pkcs1_decrypt(&context, havege_random, &random_state, 
          RSA_PRIVATE, &temp_output_size, input, current, out_part_size) != 0)
          abort_crypto_lib("Decryption failed");
        
        input += in_part_size;
        current += out_part_size;
      }
    }
    rsa_free(&context);
  }
  else
    abort_crypto_lib("Invalid key for crypt operation");

  free(key_value);
  
  debug_print("end crypt_core");
  print_buffer(*output, output_size);

  return output_size;
}

struct item *crypt(int mode, struct item *key, struct item *item)
{
  unsigned char *input = 0;
  size_t input_size = get_input(mode, &input, item);

  unsigned char *output = 0;
  size_t output_size = 0;
  
  output_size = 
          crypt_core(&output, mode, key, input, input_size);
  struct item *result = get_output(mode, output, output_size);  

  free(input);
  free(output);

  return result;
}

struct item *encrypt(struct item *key, struct item *item)
{
  debug_print("ENCRYPTING\n");
  print_item(item);

  return  crypt(ENCRYPT, key, item);;
}

struct item *decrypt(struct item *key, struct item *item)
{
  debug_print("DECRYPTING\n");
  print_item(item);
  
  return crypt(DECRYPT, key, item);
}

///////////////////////////////////////////////////////////////////////////////
// Pair item //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *create_pair(struct item *first, struct item *second)
{
  unsigned char* b_first = 0;
  unsigned char* b_second = 0;
  size_t s_first = item_serialize(&b_first, first);
  size_t s_second = item_serialize(&b_second, second);
  
  size_t size = sizeof(size_t) + s_first + s_second;
  unsigned char *buffer = malloc_wrapper(size);
  
  unsigned char *temp = buffer;
  memcpy(temp, &s_first, sizeof(size_t));
  temp += sizeof(size_t);
  memcpy(temp, b_first, s_first);
  temp += s_first;
  memcpy(temp, b_second, s_second);
  
  struct item *pair = item_create_initialized(5, buffer, size);

  free(b_first);
  free(b_second);
  free(buffer);

  return pair;
}

bool is_pair(struct item *item)
{
  return item->tag == 5;
}

void check_is_pair(struct item *item)
{
  if (!is_pair(item))
    abort_crypto_lib("Presented item is not a pair item");
}

struct item *pair_get_first(struct item *pair)
{
  check_is_pair(pair);
  unsigned char* f_serialized = pair->content + sizeof(size_t);

  struct item *result = item_deserialize(f_serialized);

  return result;
}

struct item *pair_get_second(struct item *pair)
{
  check_is_pair(pair);
  unsigned char* s_serialized = 
                  pair->content + sizeof(size_t) + *((size_t*) pair->content);

  struct item *result = item_deserialize(s_serialized);

  return result;
}

///////////////////////////////////////////////////////////////////////////////
// Network ////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct network_status
{
  int initialized;
  
  int listen_socket;
  int client_socket;
  int server_socket;
};

struct network_status *network_status_initialize()
{
  struct network_status *stat = malloc_wrapper(sizeof(struct network_status));
  
  stat->listen_socket = -1;
  stat->client_socket = -1;
  stat->server_socket = -1;

  stat->initialized = 1;

  return stat;
}

bool network_status_is_initialized(struct network_status *stat)
{
  if (stat != 0)
    return stat->initialized == 1;
  else
    return false;
}

void network_disconnect(struct network_status *stat)
{
  if(stat != 0)
  {
    if (network_status_is_initialized(stat))
    {
      if (stat->client_socket != -1)
        net_close(stat->client_socket);
      
      if (stat->listen_socket != -1)
        net_close(stat->listen_socket);
      
      if (stat->server_socket != -1)
        net_close(stat->server_socket);
      free(stat);
    }
    else
      abort_crypto_lib("Network status was not initialized");
  }
}

struct network_status *network_bind(int port)
{
  struct network_status *stat = network_status_initialize();
  
  if(net_bind(&stat->listen_socket, NULL, port) != 0)
  {
    debug_print("Failed to bind to port");
    network_disconnect(stat);
    stat = 0;
  }

  return stat;
}

void network_accept(struct network_status *stat)
{
  if(!network_status_is_initialized(stat))
    abort_crypto_lib("Network status was not initialized");
  
  if (stat->listen_socket > 0 && stat->client_socket == -1)
  {
    if(net_accept(stat->listen_socket, &stat->client_socket, NULL) != 0 ||
      net_set_block(stat->client_socket) != 0)
    {
      network_disconnect(stat);
    }
  }
}

struct network_status *network_connect(const char *name, int port)
{
  struct network_status *stat = network_status_initialize();
  
  for (int i = 0; i < 10; i++)
  {
    if(net_connect(&stat->server_socket, name, port) != 0 ||
      net_set_block(stat->server_socket) != 0)
    {
      usleep(10 * pow(2, i));
    }
    else
    {
      return stat;
    }
  }

  free(stat);
  return 0;
}

void network_send(struct network_status *stat, struct item* item)
{
  debug_print("network_send");
  print_item(item);
  
  if (network_status_is_initialized(stat))
  {
    unsigned char* message = 0;
    size_t message_size = item_serialize(&message, item);
    size_t total_size = message_size + sizeof(size_t);
    unsigned char* total_message = malloc(total_size);
    
    memcpy(total_message, &message_size, sizeof(size_t));
    memcpy(total_message + sizeof(size_t), message, message_size);
    
    if (stat->listen_socket > 0)
    {
      network_accept(stat);
      
      net_send(&stat->client_socket, total_message, total_size);
    }
    else if (stat->server_socket > 0)
    {
      net_send(&stat->server_socket, total_message, total_size);
    }
    free(total_message);
    free(message);
  }
}

struct item *network_receive_attempt(struct network_status *stat)
{
  debug_print("network_receive");

  struct item *result = 0;
  
  if (network_status_is_initialized(stat))
  {
    unsigned char receive_buffer[MAX_PACKAGE_SIZE];
    
    //Socket to use
    int *socket = 0;   
    if (stat->listen_socket > 0)
    {
      network_accept(stat); 
      socket = &stat->client_socket;
    }
    else 
    {
      socket = &stat->server_socket;
    } 
    
    //Size of the message
    size_t message_size = 0;
    if (net_recv(socket, 
            (unsigned char*) &message_size, sizeof(size_t)) != sizeof(size_t))
      return 0;
    
    if (message_size >= MAX_PACKAGE_SIZE)
      return 0;
    
    size_t received_size = net_recv(socket, receive_buffer, message_size);
    
    if (received_size != message_size)
      return 0;

    result = item_deserialize(receive_buffer);
  }
  
  if (result != 0)
    print_item(result);
  
  debug_print("network_receive done!!!!!!!!!");
  
  return result;
}

struct item *network_receive(struct network_status *stat)
{
  struct item *i = network_receive_attempt(stat);
  if (i == 0)
    abort_crypto_lib("Receiving message failed");

  return i;
}

///////////////////////////////////////////////////////////////////////////////
// Attacker capabilities //////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

int create_principal(struct item **key_sym_pp, struct keypair **pair_pp)
{
  int id = random_int();
  
  *key_sym_pp = create_key();
  *pair_pp = create_keypair(id);
  
  return id;
}



