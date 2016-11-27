#ifndef POLARSSL_MACRO_DEFINES
#define POLARSSL_MACRO_DEFINES

#include "../general_definitions/general_definitions.h"

#include <stddef.h>
#include <limits.h>
#include <stdbool.h>

//Byte sizes of different PolarSSL structs
#define HAVEGE_STATE_SIZE 36880
#define AES_CONTEXT_SIZE  280
#define GCM_CONTEXT_SIZE  388

//Some PolarSSL cryptographic algorithm configuration constants
#define POLARSSL_CIPHER_ID_AES 2
#define POLARSSL_PK_RSA        1
#define POLARSSL_MD_NONE       0

//Some self defined size limits
#define MAX_MESSAGE_SIZE 65536
#define MIN_RANDOM_SIZE 4

#endif

