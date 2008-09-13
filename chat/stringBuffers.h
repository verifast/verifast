struct string_buffer;

struct string_buffer *create_string_buffer();
char *string_buffer_get_chars(struct string_buffer *buffer);
int string_buffer_get_length(struct string_buffer *buffer);
void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count);
struct string_buffer *string_buffer_copy(struct string_buffer *buffer);
bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0);
void string_buffer_dispose(struct string_buffer *buffer);
