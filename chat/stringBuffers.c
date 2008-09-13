#include "bool.h"
#include "stringBuffers.h"
#include <malloc.h>
#include <string.h>

struct string_buffer {
    int length;
    char *chars;
};

struct string_buffer *create_string_buffer()
{
    struct string_buffer *buffer = malloc(sizeof(struct string_buffer));
    buffer->length = 0;
    buffer->chars = 0;
    return buffer;
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
{
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    copy->length = buffer->length;
    char *chars = malloc(buffer->length);
    memcpy(chars, buffer->chars, buffer->length);
    copy->chars = chars;
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
{
    return buffer->length == buffer0->length && memcmp(buffer->chars, buffer0->chars, buffer->length) == 0;
}

void string_buffer_dispose(struct string_buffer *buffer)
{
    free(buffer->chars);
    free(buffer);
}
