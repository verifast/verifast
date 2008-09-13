struct string_buffer;

struct string_buffer *create_string_buffer();
struct string_buffer *string_buffer_copy(struct string_buffer *buffer);
bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0);
void string_buffer_dispose(struct string_buffer *buffer);
