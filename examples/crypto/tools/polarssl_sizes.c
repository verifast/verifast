#include <stdlib.h>
#include <stdio.h>

#include <pthread.h>

#include "havege.h"
#include "aes.h"
#include "rsa.h"
#include "pk.h"

int main()
{
  FILE* f = fopen("polarssl_sizes.h", "w+");
  
  fprintf(f, "#ifndef POLARSSL_SIZES\n");
  fprintf(f, "#define POLARSSL_SIZES\n");
  fprintf(f, "\n");
  fprintf(f, "#define CHAR_SIZE_OF_HAVEGE_STATE %i\n", sizeof(havege_state) / sizeof(char));
  fprintf(f, "#define CHAR_SIZE_OF_AES_CONTEXT %i\n", sizeof(aes_context) / sizeof(char));
  fprintf(f, "#define PK_RSA_TYPE %i\n", POLARSSL_PK_RSA);
  fprintf(f, "\n");
  fprintf(f, "#endif\n");
  fprintf(f, "\n");
  fflush(f);
  
  fclose(f);
  
  return 0;
}
