char *string_buffer_get_chars(struct string_buffer *buffer);
int string_buffer_get_length(struct string_buffer *buffer);
void string_buffer_clear(struct string_buffer *buffer);
void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count);
