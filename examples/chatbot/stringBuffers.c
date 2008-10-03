#include "bool.h"
#include "stringBuffers.h"
#include "stringBuffersExt.h"
#include <malloc.h>
#include <string.h>

struct string_buffer {
    int length;
    int capacity;
    char *chars;
};

struct string_buffer *create_string_buffer()
{
    struct string_buffer *buffer = malloc(sizeof(struct string_buffer));
    buffer->length = 0;
    buffer->capacity = 0;
    buffer->chars = 0;
    return buffer;
}

char *string_buffer_get_chars(struct string_buffer *buffer)
{
    return buffer->chars;
}

int string_buffer_get_length(struct string_buffer *buffer)
{
    return buffer->length;
}

void string_buffer_clear(struct string_buffer *buffer)
{
	buffer->length = 0;
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
{
    int newLength = buffer->length + count;
    if (newLength > buffer->capacity) {
        char *newChars = malloc(newLength);
        buffer->capacity = newLength;
        memcpy(newChars, buffer->chars, buffer->length);
        free(buffer->chars);
        buffer->chars = newChars;
    }
    memcpy(buffer->chars + buffer->length, chars, count);
    buffer->length = newLength;
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
{
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc(buffer->length);
    copy->length = buffer->length;
    copy->capacity = buffer->length;
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


bool string_buffer_equals_string(struct string_buffer *buffer, char *text)
{
	char *buffer_text = string_buffer_get_chars(buffer);
	return buffer->length == strlen(text) && memcmp(buffer_text,text,strlen(text)) == 0;
}

bool string_buffer_split_string(struct string_buffer *orig_buffer, const char *split_text, struct string_buffer *buffer1, struct string_buffer *buffer2)
{
	char* result;
	int orig_length = 0;
	char* orig_text = malloc(orig_buffer->length + 1);
	orig_text[0]='\0';
	strncat(orig_text,orig_buffer->chars,orig_buffer->length);
	result = strstr(orig_text,split_text);
	orig_length = orig_buffer->length;
	if(result == NULL || orig_length <= 0 )
	{
		return false;
	}
	else
	{		
		int tok_length = strlen(split_text);
		int text2_length = strlen(result);
		string_buffer_clear(buffer1);
		string_buffer_append_chars(buffer1, orig_text, orig_length - text2_length);
		string_buffer_clear(buffer2);
		string_buffer_append_chars(buffer2, result + tok_length, text2_length - tok_length);
		return true;
	}
}