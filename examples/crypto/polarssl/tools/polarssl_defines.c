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
  FILE* f = fopen("polarssl_defines.h", "w+");
  
  fprintf(f, "#ifndef POLARSSL_DEFINES\n");
  fprintf(f, "#define POLARSSL_DEFINES\n");
  fprintf(f, "\n");
  fprintf(f, "#define POLARSSL_CHAR_SIZE_OF_HAVEGE_STATE %i\n", sizeof(havege_state) / sizeof(char));
  fprintf(f, "#define POLARSSL_CHAR_SIZE_OF_AES_CONTEXT %i\n", sizeof(aes_context) / sizeof(char));
  fprintf(f, "#define POLARSSL_AES_CIPHER_ID %i\n", POLARSSL_CIPHER_ID_AES);
  fprintf(f, "#define POLARSSL_CHAR_SIZE_OF_GCM_CONTEXT %i\n", sizeof(gcm_context) / sizeof(char));
  fprintf(f, "#define POLARSSL_PK_RSA_TYPE %i\n", POLARSSL_PK_RSA);
  fprintf(f, "#define POLARSSL_MD_NONE %i\n", POLARSSL_MD_NONE);
  fprintf(f, "\n");
  fprintf(f, "#endif\n");
  fprintf(f, "\n");
  fflush(f);
  
  fclose(f);
  
  return 0;
}
