#ifndef POLARSSL_MACRO_DEFINES
#define POLARSSL_MACRO_DEFINES

#include <stdlib.h>
#include "crypto.h"
#include <stddef.h>
#include <limits.h>
#include <stdbool.h>

//Byte sizes of different PolarSSL structs
#define HAVEGE_STATE_SIZE 36880
#define AES_CONTEXT_SIZE  280
#define GCM_CONTEXT_SIZE  388

//Some PolarSSL cryptographic algorithm configuration constants
#define MBEDTLS_CIPHER_ID_AES 2
#define MBEDTLS_PK_RSA        1
#define MBEDTLS_MD_NONE       0

//Some self defined size limits
#define ID_SIZE 12
#define MAX_MESSAGE_SIZE 65536
#define MIN_RANDOM_SIZE 4
#define MINIMAL_STRING_SIZE 10

#endif

