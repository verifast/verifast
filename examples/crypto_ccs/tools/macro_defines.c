#include <stdlib.h>
#include <stdio.h>

#include <pthread.h>

#include "havege.h"
#include "aes.h"
#include "gcm.h"
#include "cipher.h"
#include "pk.h"

int main()
{
  FILE* f = fopen("macro_defines.h", "w+");
  
  fprintf(f, "#ifndef POLARSSL_MACRO_DEFINES\n");
  fprintf(f, "#define POLARSSL_MACRO_DEFINES\n");
  fprintf(f, "\n");
  fprintf(f, "#include <stdlib.h>\n");
  fprintf(f, "#include <stddef.h>\n");
  fprintf(f, "#include <limits.h>\n");
  fprintf(f, "#include <stdbool.h>\n");
  fprintf(f, "\n");
  
  fprintf(f, "//Byte sizes of different PolarSSL structs\n");
  fprintf(f, "#define HAVEGE_STATE_SIZE %i\n", sizeof(havege_state) / sizeof(char));
  fprintf(f, "#define AES_CONTEXT_SIZE  %i\n", sizeof(aes_context) / sizeof(char));
  fprintf(f, "#define GCM_CONTEXT_SIZE  %i\n", sizeof(gcm_context) / sizeof(char));
  fprintf(f, "\n");
  fprintf(f, "//Some PolarSSL cryptographic algorithm configuration constants\n");
  fprintf(f, "#define MBEDTLS_CIPHER_ID_AES %i\n", POLARSSL_CIPHER_ID_AES);
  fprintf(f, "#define MBEDTLS_PK_RSA        %i\n", POLARSSL_PK_RSA);
  fprintf(f, "#define MBEDTLS_MD_NONE       %i\n", POLARSSL_MD_NONE);
  fprintf(f, "\n");
  fprintf(f, "//Some self defined size limits\n");
  fprintf(f, "#define ID_SIZE 12\n");
  fprintf(f, "#define MAX_MESSAGE_SIZE 65536\n");
  fprintf(f, "#define MIN_RANDOM_SIZE 4\n");
  fprintf(f, "#define MINIMAL_STRING_SIZE 10\n");
  fprintf(f, "\n");
  
  fprintf(f, "#endif\n");
  fprintf(f, "\n");
  fflush(f);
  
  fclose(f);
  
  return 0;
}
