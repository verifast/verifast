#ifndef UINT_PRELUDE_H
#define UINT_PRELUDE_H

/*@

// unsigned int <-> chars ...
fixpoint unsigned int uint_of_chars(list<char> cs);
fixpoint list<char> chars_of_uint(unsigned int i);

lemma_auto(uint_of_chars(chars_of_uint(i))) void uint_of_chars_of_uint(unsigned int i);
    requires 0 <= i && i <= UINT_MAX;
    ensures i == (uint_of_chars(chars_of_uint(i)));

lemma_auto(chars_of_uint(uint_of_chars(cs))) void chars_of_uint_of_chars(list<char> cs);
    requires true;
    ensures cs == (chars_of_uint(uint_of_chars(cs)));

lemma void uint_of_chars_injective(list<char> cs1, list<char> cs2);
    requires true;
    ensures true == ((cs1 == cs2) == (uint_of_chars(cs1) == uint_of_chars(cs2)));

lemma void chars_of_uint_injective(unsigned int i1, unsigned int i2);
    requires true;
    ensures true == ((i1 == i2) == (chars_of_uint(i1) == chars_of_uint(i2)));

lemma_auto void chars_of_uint_size(unsigned int i);
    requires 0 <= i && i <= UINT_MAX;
    ensures length(chars_of_uint(i)) == sizeof(unsigned int);

lemma_auto void uint_of_chars_size(list<char> cs);
    requires length(cs) == sizeof(unsigned int) && chars_within_limits(cs);
    ensures 0 <= uint_of_chars(cs) && uint_of_chars(cs) <= UINT_MAX;

lemma void chars_of_uint_char_in_bounds(char c, unsigned int i);
    requires 0 <= i && i <= UINT_MAX &*&
             true == mem(c, chars_of_uint(i));
    ensures  INT_MIN <= c && c <= INT_MAX;

// chars to ...

lemma_auto void my_chars_to_u_integer(void *p);
    requires [?f]chars(p, sizeof(unsigned int), ?cs);
    ensures [f]u_integer(p, uint_of_chars(cs));


// ... to chars

lemma_auto void my_u_integer_to_chars(void *p);
    requires [?f]u_integer(p, ?i);
    ensures [f]chars(p, sizeof(unsigned int), chars_of_uint(i));


@*/


#endif
