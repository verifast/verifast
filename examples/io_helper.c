#include "stdio.h"
#include <stdbool.h>

int read_int()
{
    int value = 0;
    while (true)
    {
        int result = scanf("%d\n", &value);
        if (result == EOF) abort();
        if (result == 1) break;
        puts("Please enter a number.");
    }
    return value;
}

char *read_string()
{
    int n;
    char *buffer = malloc(40);
    char *result = fgets(buffer, 40, stdin);
    if (result == 0) abort();
    n = strlen(buffer);
    if (n > 0 && buffer[n - 1] == '\n')
        buffer[n - 1] = 0;
    return buffer;
}
