#ifndef PRELUDE_H
#define PRELUDE_H

//@ #include "prelude_core.gh"
//@ #include "list.gh"

/*@

lemma void assume(bool b);
    requires true;
    ensures b;

predicate exists<t>(t x;) = true;

fixpoint int truncate_unsigned(int x, int nbBits);
fixpoint int truncate_signed(int x, int nbBits); // nbBits does not include the sign bit

fixpoint int abs(int x) { return x < 0 ? -x : x; }

lemma void mul_mono_l(int x, int y, int z);
    requires x <= y &*& 0 <= z;
    ensures x * z <= y * z;

lemma void div_rem(int D, int d);
    requires d != 0;
    ensures D == D / d * d + D % d &*& abs(D % d) < abs(d) &*& abs(D / d * d) <= abs(D);

lemma void div_rem_nonneg(int D, int d);
    requires 0 <= D &*& 0 < d;
    ensures D == D / d * d + D % d &*& 0 <= D / d &*& D / d <= D &*& 0 <= D % d &*& D % d < d;

predicate integer_(void *p, int size, bool signed_; int v);

predicate character(char *p; char c) = integer_(p, 1, true, c);
predicate u_character(unsigned char *p; unsigned char c) = integer_(p, 1, false, c);

predicate integer(int *p; int v) = integer_(p, sizeof(int), true, v);
predicate u_integer(unsigned int *p; unsigned int v) = integer_(p, sizeof(int), false, v);

predicate llong_integer(long long *p; long long l) = integer_(p, sizeof(long long), true, l);
predicate u_llong_integer(unsigned long long *p; unsigned long long l) = integer_(p, sizeof(long long), false, l);

predicate short_integer(short *p; short s) = integer_(p, sizeof(short), true, s);
predicate u_short_integer(unsigned short *p; unsigned short v) = integer_(p, sizeof(short), false, v);

predicate pointer(void **pp; void *p);

predicate boolean(bool* p; bool v);

predicate float_(float *p; float v);
predicate double_(double *p; double v);
predicate long_double(long double *p; long double v);

lemma void character_limits(char *pc);
    requires [?f]character(pc, ?c);
    ensures [f]character(pc, c) &*& pc > (char *)0 &*& pc < (char *)UINTPTR_MAX &*& -128 <= c &*& c <= 127;

lemma void u_character_limits(unsigned char *pc);
    requires [?f]u_character(pc, ?c);
    ensures [f]u_character(pc, c) &*& pc > (unsigned char *)0 &*& pc < (unsigned char *)UINTPTR_MAX &*& 0 <= c &*& c <= 255;

lemma void integer_distinct(int* i, int* j);
    requires integer(i, ?v1) &*& integer(j, ?v2);
    ensures integer(i, v1) &*& integer(j, v2) &*& i != j;

lemma void integer_unique(int *p);
    requires [?f]integer(p, ?v);
    ensures [f]integer(p, v) &*& f <= 1;

lemma void integer_limits(int *p);
    requires [?f]integer(p, ?v);
    ensures [f]integer(p, v) &*& p > (int *)0 &*& p + 1 <= (int *)UINTPTR_MAX &*& INT_MIN <= v &*& v <= INT_MAX;

lemma void u_integer_limits(unsigned int *p);
    requires [?f]u_integer(p, ?v);
    ensures [f]u_integer(p, v) &*& p > (unsigned int *)0 &*& p + 1 <= (unsigned int *)UINTPTR_MAX &*& 0 <= v &*& v <= UINT_MAX;

lemma void short_integer_limits(short *p);
    requires [?f]short_integer(p, ?v);
    ensures [f]short_integer(p, v) &*& p > (short *)0 &*& p + 1 <= (short *)UINTPTR_MAX &*& SHRT_MIN <= v &*& v <= SHRT_MAX;

lemma void u_short_integer_limits(unsigned short *p);
    requires [?f]u_short_integer(p, ?v);
    ensures [f]u_short_integer(p, v) &*& p > (unsigned short *)0 &*& p + 1 <= (unsigned short *)UINTPTR_MAX &*& 0 <= v &*& v <= USHRT_MAX;

lemma void pointer_distinct(void *pp1, void *pp2);
    requires pointer(pp1, ?p1) &*& pointer(pp2, ?p2);
    ensures pointer(pp1, p1) &*& pointer(pp2, p2) &*& pp1 != pp2;

lemma void pointer_unique(void *pp);
    requires [?f]pointer(pp, ?p);
    ensures [f]pointer(pp, p) &*& f <= 1;

lemma_auto void pointer_nonzero();
    requires pointer(?pp, ?p);
    ensures pointer(pp, p) &*& pp != 0;

lemma void pointer_limits(void *pp);
    requires [?f]pointer(pp, ?p);
    ensures [f]pointer(pp, p) &*& pp > (void *)0 &*& pp + sizeof(void *) <= (void *)UINTPTR_MAX &*& p >= (void *)0 &*& p <= (void *)UINTPTR_MAX;

lemma void boolean_distinct(bool* i, bool* j);
    requires boolean(i, ?v1) &*& boolean(j, ?v2);
    ensures boolean(i, v1) &*& boolean(j, v2) &*& i != j;

lemma void boolean_unique(bool *p);
    requires [?f]boolean(p, ?v);
    ensures [f]boolean(p, v) &*& f <= 1;

fixpoint void *pointer_of_chars(list<char> cs);
fixpoint list<char> chars_of_pointer(void * p);
fixpoint bool chars_within_limits(list<char> cs);

lemma_auto(pointer_of_chars(chars_of_pointer(p))) void pointer_of_chars_of_pointer(void *p);
    requires p >= (void *)0 && p <= (void *)UINTPTR_MAX;
    ensures pointer_of_chars(chars_of_pointer(p)) == p && chars_within_limits(chars_of_pointer(p)) == true && length(chars_of_pointer(p)) == sizeof(void *);

lemma_auto(chars_of_pointer(pointer_of_chars(cs))) void chars_of_pointer_of_chars(list<char> cs);
    requires length(cs) == sizeof(void *) && chars_within_limits(cs) == true;
    ensures chars_of_pointer(pointer_of_chars(cs)) == cs;


predicate chars(char *array, int count; list<char> cs) =
    count == 0 ?
        cs == nil
    :
        character(array, ?c) &*& chars(array + 1, count - 1, ?cs0) &*& cs == cons(c, cs0);

lemma_auto void chars_inv();
    requires [?f]chars(?array, ?count, ?cs);
    ensures [f]chars(array, count, cs) &*& length(cs) == count;

lemma void chars_zero();
    requires [?f]chars(0, _, ?cs);
    ensures cs == nil;

lemma void chars_limits(char *array);
    requires [?f]chars(array, ?n, ?cs) &*& (char *)0 <= array &*& array <= (char *)UINTPTR_MAX;
    ensures [f]chars(array, n, cs) &*& (char *)0 <= array &*& array + n <= (char *)UINTPTR_MAX;

lemma_auto void chars_split(char *array, int offset);
   requires [?f]chars(array, ?n, ?cs) &*& 0 <= offset &*& offset <= n;
   ensures
       [f]chars(array, offset, take(offset, cs))
       &*& [f]chars(array + offset, n - offset, drop(offset, cs))
       &*& append(take(offset, cs), drop(offset, cs)) == cs;

lemma_auto void chars_join(char *array);
    requires [?f]chars(array, ?n, ?cs) &*& [f]chars(array + n, ?n0, ?cs0);
    ensures [f]chars(array, n + n0, append(cs, cs0));

fixpoint int int_of_chars(list<char> cs);
fixpoint list<char> chars_of_int(int i);

lemma_auto(int_of_chars(chars_of_int(i))) void int_of_chars_of_int(int i);
    requires INT_MIN <= i && i <= INT_MAX;
    ensures i == (int_of_chars(chars_of_int(i)));

lemma_auto(chars_of_int(int_of_chars(cs))) void chars_of_int_of_chars(list<char> cs);
    requires true;
    ensures cs == (chars_of_int(int_of_chars(cs)));

lemma void int_of_chars_injective(list<char> cs1, list<char> cs2);
    requires true;
    ensures (cs1 == cs2) == (int_of_chars(cs1) == int_of_chars(cs2));

lemma void chars_of_int_injective(int i1, int i2);
    requires true;
    ensures (i1 == i2) == (chars_of_int(i1) == chars_of_int(i2));

lemma_auto void chars_of_int_size(int i);
    requires INT_MIN <= i && i <= INT_MAX;
    ensures length(chars_of_int(i)) == sizeof(int);

lemma_auto void int_of_chars_size(list<char> cs);
    requires length(cs) == sizeof(int) && chars_within_limits(cs);
    ensures INT_MIN <= int_of_chars(cs) && int_of_chars(cs) <= INT_MAX;

lemma void chars_of_int_char_in_bounds(char c, int i);
    requires INT_MIN <= i && i <= INT_MAX &*&
             true == mem(c, chars_of_int(i));
    ensures  INT_MIN <= c && c <= INT_MAX;

// chars to ...
lemma_auto void chars_to_integer(void *p);
    requires [?f]chars(p, sizeof(int), ?cs);
    ensures [f]integer(p, int_of_chars(cs));

lemma_auto void chars_to_u_integer(void *p);
    requires [?f]chars(p, sizeof(unsigned int), ?cs);
    ensures [f]u_integer(p, _);

lemma_auto void chars_to_short_integer(void *p);
    requires [?f]chars(p, sizeof(short), ?cs);
    ensures [f]short_integer(p, _);

lemma_auto void chars_to_u_short_integer(void *p);
    requires [?f]chars(p, sizeof(unsigned short), ?cs);
    ensures [f]u_short_integer(p, _);

lemma_auto void chars_to_pointer(void *p);
    requires [?f]chars(p, sizeof(void *), ?cs);
    ensures [f]pointer(p, pointer_of_chars(cs));

lemma_auto void chars_to_integer_(void *p, int size, bool signed_);
    requires [?f]chars(p, size, ?cs);
    ensures [f]integer_(p, size, signed_, _);

// ... to chars
lemma_auto void integer_to_chars(void *p);
    requires [?f]integer(p, ?i);
    ensures [f]chars(p, sizeof(int), chars_of_int(i));

lemma_auto void u_integer_to_chars(void *p);
    requires [?f]u_integer(p, _);
    ensures [f]chars(p, sizeof(unsigned int), ?cs);

lemma_auto void short_integer_to_chars(void *p);
    requires [?f]short_integer(p, _);
    ensures [f]chars(p, sizeof(short), ?cs);

lemma_auto void u_short_integer_to_chars(void *p);
    requires [?f]u_short_integer(p, _);
    ensures [f]chars(p, sizeof(unsigned short), ?cs);

lemma_auto void pointer_to_chars(void *p);
    requires [?f]pointer(p, ?v);
    ensures [f]chars(p, sizeof(void *), chars_of_pointer(v));

lemma_auto void integer__to_chars(void *p, int size, bool signed_);
    requires [?f]integer_(p, size, signed_, ?v);
    ensures [f]chars(p, size, _);

// u_character to/from character
lemma_auto void u_character_to_character(void *p);
    requires [?f]u_character(p, _);
    ensures [f]character(p, _);

lemma_auto void character_to_u_character(void *p);
    requires [?f]character(p, _);
    ensures [f]u_character(p, _);


predicate uchars(unsigned char *p, int count; list<unsigned char> cs) =
    true == ((unsigned char *)0 <= p) &*& p <= (unsigned char *)UINTPTR_MAX &*&
    count == 0 ?
        cs == nil
    :
        u_character(p, ?c) &*& uchars(p + 1, count - 1, ?cs0) &*& cs == cons(c, cs0);

lemma_auto void uchars_inv();
    requires [?f]uchars(?p, ?count, ?cs);
    ensures [f]uchars(p, count, cs) &*& count == length(cs) &*& true == ((char *)0 <= (void *)p) &*& p + count <= (void *)UINTPTR_MAX;

lemma_auto void uchars_split(unsigned char *array, int offset);
   requires [?f]uchars(array, ?n, ?cs) &*& 0 <= offset &*& offset <= n;
   ensures
       [f]uchars(array, offset, take(offset, cs))
       &*& [f]uchars(array + offset, n - offset, drop(offset, cs))
       &*& append(take(offset, cs), drop(offset, cs)) == cs;

lemma_auto void uchars_join(unsigned char *array);
    requires [?f]uchars(array, ?n, ?cs) &*& [f]uchars((void *)array + n, ?n0, ?cs0);
    ensures [f]uchars(array, n + n0, append(cs, cs0));

predicate ints(int *p, int count; list<int> vs) =
    count == 0 ?
        vs == nil
    :
        integer(p, ?v) &*& ints(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

lemma_auto void ints_inv();
    requires [?f]ints(?p, ?count, ?vs);
    ensures [f]ints(p, count, vs) &*& count == length(vs);

predicate uints(unsigned int *p, int count; list<unsigned int> vs) =
    count == 0 ?
        vs == nil
    :
        u_integer(p, ?v) &*& uints(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

lemma_auto void uints_inv();
    requires [?f]uints(?p, ?count, ?vs);
    ensures [f]uints(p, count, vs) &*& count == length(vs);

predicate llongs(long long *p, int count; list<long long> ls) = 
    count == 0 ?
        ls == nil
    :
        llong_integer(p, ?l) &*& llongs(p + 1, count - 1, ?ls0) &*& ls == cons(l, ls0);

lemma_auto void llongs_inv();
    requires [?f]llongs(?p, ?count, ?vs);
    ensures [f]llongs(p, count, vs) &*& count == length(vs);

predicate ullongs(unsigned long long *p, int count; list<unsigned long long> ls) = 
    count == 0 ?
        ls == nil
    :
        u_llong_integer(p, ?l) &*& ullongs(p + 1, count - 1, ?ls0) &*& ls == cons(l, ls0);

lemma_auto void ullongs_inv();
    requires [?f]ullongs(?p, ?count, ?vs);
    ensures [f]ullongs(p, count, vs) &*& count == length(vs);

predicate shorts(short *p, short count; list<short> vs) =
    count == 0 ?
        vs == nil
    :
        short_integer(p, ?v) &*& shorts(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

lemma_auto void shorts_inv();
    requires [?f]shorts(?p, ?count, ?vs);
    ensures [f]shorts(p, count, vs) &*& count == length(vs);

predicate ushorts(unsigned short *p, short count; list<unsigned short> vs) =
    count == 0 ?
        vs == nil
    :
        u_short_integer(p, ?v) &*& ushorts(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

lemma_auto void ushorts_inv();
    requires [?f]ushorts(?p, ?count, ?vs);
    ensures [f]ushorts(p, count, vs) &*& count == length(vs);

predicate bools(bool *p, int count; list<bool> vs) =
    count == 0 ?
        vs == nil
    :
        boolean(p, ?v) &*& bools(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

predicate pointers(void **pp, int count; list<void *> ps) =
    count == 0 ?
        ps == nil
    :
        pointer(pp, ?p) &*& pointers(pp + 1, count - 1, ?ps0) &*& ps == cons(p, ps0);

lemma_auto void pointers_inv();
    requires [?f]pointers(?pp, ?count, ?ps);
    ensures [f]pointers(pp, count, ps) &*& count == length(ps);

lemma void pointers_limits(void **array);
    requires [?f]pointers(array, ?n, ?ps) &*& (void **)0 <= array &*& array <= (void **)UINTPTR_MAX;
    ensures [f]pointers(array, n, ps) &*& array + n <= (void **)UINTPTR_MAX;

lemma_auto void pointers_split(void **pp, int offset);
    requires [?f]pointers(pp, ?count, ?ps) &*& 0 <= offset &*& offset <= count;
    ensures [f]pointers(pp, offset, take(offset, ps)) &*& [f]pointers(pp + offset, count - offset, drop(offset, ps));

lemma_auto void pointers_join(void **pp);
    requires [?f]pointers(pp, ?count1, ?ps1) &*& [f]pointers(pp + count1, ?count2, ?ps2);
    ensures [f]pointers(pp, count1 + count2, append(ps1, ps2));

fixpoint char char_of_uchar(unsigned char c);
fixpoint unsigned char uchar_of_char(char c);

lemma_auto void map_uchar_of_char_char_of_uchar(list<unsigned char> ucs);
    requires true;
    ensures map(uchar_of_char, map(char_of_uchar, ucs)) == ucs;

lemma_auto void map_char_of_uchar_uchar_of_char(list<char> cs);
    requires true;
    ensures map(char_of_uchar, map(uchar_of_char, cs)) == cs;

lemma_auto void chars_to_uchars(void *p);
    requires [?f]chars(p, ?n, ?cs);
    ensures [f]uchars(p, n, map(uchar_of_char, cs));

lemma_auto void uchars_to_chars(void *p);
    requires [?f]uchars(p, ?n, ?ucs);
    ensures [f]chars(p, n, map(char_of_uchar, ucs));

lemma_auto void chars_to_ints(void *p, int n);
    requires [?f]chars(p, n * sizeof(int), _);
    ensures [f]ints(p, n, _);

lemma_auto void ints_to_chars(void *p);
    requires [?f]ints(p, ?n, _);
    ensures [f]chars(p, n * sizeof(int), _);

lemma_auto void chars_to_uints(void *p, int n);
    requires [?f]chars(p, n * sizeof(unsigned int), _);
    ensures [f]uints(p, n, _);

lemma_auto void uints_to_chars(void *p);
    requires [?f]uints(p, ?n, _);
    ensures [f]chars(p, n * sizeof(unsigned int), _);

lemma_auto void chars_to_integers_(void *p, int size, bool signed_, int n);
    requires [?f]chars(p, n * size, _);
    ensures [f]integers_(p, size, signed_, n, _);

lemma_auto void integers__to_chars(void *p);
    requires [?f]integers_(p, ?size, ?signed_, ?n, _);
    ensures [f]chars(p, n * size, _);

lemma_auto void uchars_to_integers_(void *p, int size, bool signed_, int n);
    requires [?f]uchars(p, n * size, _);
    ensures [f]integers_(p, size, signed_, n, _);

lemma_auto void integers__to_uchars(void *p);
    requires [?f]integers_(p, ?size, ?signed_, ?n, _);
    ensures [f]uchars(p, n * size, _);

fixpoint list<void *> pointers_of_chars(list<char> cs);
fixpoint list<char> chars_of_pointers(list<void *> ps);

lemma_auto void chars_to_pointers(void *p, int n);
    requires [?f]chars(p, n * sizeof(void *), ?cs);
    ensures [f]pointers(p, n, pointers_of_chars(cs)) &*& chars_of_pointers(pointers_of_chars(cs)) == cs;

lemma_auto void pointers_to_chars(void *pp);
    requires [?f]pointers(pp, ?n, ?ps) &*& true;
    ensures [f]chars(pp, n * sizeof(void *), chars_of_pointers(ps)) &*& pointers_of_chars(chars_of_pointers(ps)) == ps;

predicate integers_(void *p, int size, bool signed_, int count; list<int> vs) =
    count == 0 ?
        vs == nil
    :
        integer_(p, size, signed_, ?v0) &*& integers_(p + size, size, signed_, count - 1, ?vs0) &*& vs == cons(v0, vs0);

lemma_auto void integers__inv();
    requires [?f]integers_(?p, ?size, ?signed_, ?count, ?vs);
    ensures [f]integers_(p, size, signed_, count, vs) &*& length(vs) == count &*& 0 <= (uintptr_t)p &*& (uintptr_t)p <= UINTPTR_MAX;

predicate floats(float *p, int count; list<float> values) =
    count == 0 ?
        values == nil
    :
        float_(p, ?value) &*& floats(p + 1, count - 1, ?values0) &*& values == cons(value, values0);

predicate doubles(double *p, int count; list<double> values) =
    count == 0 ?
        values == nil
    :
        double_(p, ?value) &*& doubles(p + 1, count - 1, ?values0) &*& values == cons(value, values0);

predicate long_doubles(long double *p, int count; list<long double> values) =
    count == 0 ?
        values == nil
    :
        long_double(p, ?value) &*& long_doubles(p + 1, count - 1, ?values0) &*& values == cons(value, values0);

predicate divrem(int D, int d; int q, int r); // Rounds towards negative infinity, unlike C integer division and remainder.

lemma void divrem_intro(int D, int d, int q, int r);
    requires 0 <= r &*& r < d &*& D == q * d + r;
    ensures divrem(D, d, q, r);

lemma_auto void divrem_elim();
    requires divrem(?D, ?d, ?q, ?r);
    ensures divrem(D, d, q, r) &*& 0 <= r &*& r <= d &*& D == q * d + r;

predicate malloc_block(void *p; int size);
predicate malloc_block_chars(char *p; int count) = malloc_block(p, count);
predicate malloc_block_uchars(unsigned char *p; int count) = malloc_block(p, count);
predicate malloc_block_ints(int *p; int count) = malloc_block(p, ?size) &*& divrem(size, sizeof(int), count, 0);
predicate malloc_block_uints(unsigned int *p; int count) = malloc_block(p, ?size) &*& divrem(size, sizeof(unsigned int), count, 0);
predicate malloc_block_shorts(short *p; int count) = malloc_block(p, ?size) &*& divrem(size, sizeof(short), count, 0);
predicate malloc_block_ushorts(unsigned short *p; int count) = malloc_block(p, ?size) &*& divrem(size, sizeof(unsigned short), count, 0);
predicate malloc_block_pointers(void **p; int count) = malloc_block(p, ?size) &*& divrem(size, sizeof(void *), count, 0);
predicate malloc_block_llongs(long long *p; int count) = malloc_block(p, ?size) &*& divrem(size, sizeof(long long), count, 0);
predicate malloc_block_ullongs(unsigned long long *p; int count) = malloc_block(p, ?size) &*& divrem(size, sizeof(unsigned long long), count, 0);
predicate malloc_block_bools(bool *p; int count) =  malloc_block(p, ?size) &*& divrem(size, sizeof(bool), count, 0);
predicate malloc_block_floats(float *p; int count) = malloc_block(p, ?size) &*& divrem(size, sizeof(float), count, 0);
predicate malloc_block_doubles(double *p; int count) = malloc_block(p, ?size) &*& divrem(size, sizeof(double), count, 0);
predicate malloc_block_long_doubles(long double *p; int count) = malloc_block(p, ?size) &*& divrem(size, sizeof(long double), count, 0);

@*/

/*@

predicate string(char *s; list<char> cs) =
    character(s, ?c) &*&
    c == 0 ?
        cs == nil
    :
        string(s + 1, ?cs0) &*& cs == cons(c, cs0);

lemma_auto void string_to_body_chars(char *s);
    requires [?f]string(s, ?cs);
    ensures [f]chars(s, length(cs), cs) &*& [f]character(s + length(cs), 0) &*& !mem('\0', cs);

lemma_auto void body_chars_to_string(char *s);
    requires [?f]chars(s, _, ?cs) &*& [f]character(s + length(cs), 0) &*& !mem('\0', cs);
    ensures [f]string(s, cs);

lemma_auto void chars_to_string(char *s);
    requires [?f]chars(s, ?n, ?cs) &*& index_of('\0', cs) == n - 1;
    ensures [f]string(s, take(n - 1, cs));

lemma_auto void string_to_chars(char *s);
    requires [?f]string(s, ?cs);
    ensures [f]chars(s, length(cs) + 1, append(cs, cons('\0', nil))) &*& !mem('\0', cs);

lemma_auto void chars_separate_string(char *s);
    requires [?f]chars(s, ?n, ?cs) &*& mem('\0', cs) == true;
    ensures [f]string(s, take(index_of('\0', cs), cs)) &*& [f]chars(s + index_of('\0', cs) + 1, n - index_of('\0', cs) - 1, drop(index_of('\0', cs) + 1, cs));

lemma_auto void chars_unseparate_string(char *s);
    requires [?f]string(s, ?cs) &*& [f]chars(s + length(cs) + 1, ?n, ?cs1);
    ensures [f]chars(s, length(cs) + 1 + n, append(cs, cons('\0', cs1)));

lemma void string_limits(char *s);
    requires [?f]string(s, ?cs);
    ensures [f]string(s, cs) &*& true == ((char *)0 < s) &*& s + length(cs) < (char *)UINTPTR_MAX;

inductive vararg = vararg_int(int) | vararg_uint(unsigned int) | vararg_pointer(void *);

@*/

/*@

// Termination of function pointer calls

fixpoint bool func_lt(void *f, void *g);

predicate call_perm_(void *f;);
predicate call_below_perm_(void *f;);

@*/

/*@

predicate module(int moduleId, bool initialState);
predicate module_code(int moduleId;);

predicate argv(char **argv, int argc; list<list<char> > arguments) =
    argc <= 0 ?
        pointer(argv, 0) &*& arguments == nil
    :
        pointer(argv, ?arg)
        &*& string(arg, ?head_arguments)
        &*& argv(argv + 1, argc - 1, ?tail_arguments)
        &*& arguments == cons(head_arguments, tail_arguments); // fix output parameter.
@*/

typedef int main(int argc, char **argv);
    //@ requires 0 <= argc &*& [_]argv(argv, argc, ?arguments);
    //@ ensures true;

typedef int main_full/*@(int mainModule)@*/(int argc, char **argv);
    //@ requires module(mainModule, true) &*& [_]argv(argv, argc, ?arguments);
    //@ ensures true;

// action permissions

/*@
fixpoint bool is_action_permission0(predicate(box;) p);

lemma void action_permission0_unique(predicate(box;) p, box id);
  requires [?f]p(id) &*& is_action_permission0(p) == true;
  ensures [f]p(id) &*& f <= 1;
  
fixpoint bool is_action_permission1_dispenser<t>(predicate(box, list<t>) p);
fixpoint predicate(box, t) get_action_permission1_for_dispenser<t>(predicate(box, list<t>) p);

lemma void action_permission1_split<t>(predicate(box, list<t>) dispenser, predicate(box, t) p, box id, t x);
  requires is_action_permission1_dispenser(dispenser) == true &*& dispenser(id, ?used) &*& ! mem(x, used) &*& get_action_permission1_for_dispenser(dispenser) == p;
  ensures dispenser(id, cons(x, used)) &*& p(id, x);

lemma void action_permission1_split2<t>(predicate(box, list<t>) dispenser, predicate(box, t) p, box id, t x);
  requires is_action_permission1_dispenser(dispenser) == true &*& dispenser(id, ?used) &*& ! mem(x, used) &*& get_action_permission1_for_dispenser(dispenser) == p;
  ensures dispenser(id, append(used, cons(x, nil))) &*& p(id, x);

lemma void action_permission1_merge<t>(predicate(box, list<t>) dispenser, predicate(box, t) p, box id, t x);
  requires is_action_permission1_dispenser(dispenser) == true &*& dispenser(id, ?used) &*& get_action_permission1_for_dispenser(dispenser) == p &*& p(id, x);
  ensures dispenser(id, remove(x, used));
  
fixpoint bool is_action_permission1<t>(predicate(box, t;) p);

lemma void action_permission1_unique<t>(predicate(box, t;) p, box id, t x);
  requires [?f]p(id, x) &*& is_action_permission1<t>(p) == true;
  ensures [f]p(id, x) &*& f <= 1;
  
predicate is_handle(handle ha);

lemma void is_handle_unique(handle ha1, handle ha2);
  requires is_handle(ha1) &*& is_handle(ha2);
  ensures is_handle(ha1) &*& is_handle(ha2) &*& ha1 != ha2;

lemma void box_level_unique(box id1, box id2);
  requires id1 != id2;
  ensures box_level(id1) != box_level(id2);

fixpoint real box_level(box id);

predicate current_box_level(real level);
@*/

#endif
