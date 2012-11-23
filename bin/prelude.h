#ifndef PRELUDE_H
#define PRELUDE_H

//@ #include "prelude_core.gh"
//@ #include "list.gh"

/*@

lemma void assume(bool b);
    requires true;
    ensures b;

@*/

//@ predicate exists<t>(t x;) = true;

/*@
predicate array<t>(void* a, int n, int elemsize, predicate(t*; t) q; list<t> elems) =
  n == 0 ?
    elems == nil
  :
    q(a, ?elem) &*& array<t>(a + elemsize, n - 1, elemsize, q, ?elems0) &*& elems == cons(elem, elems0);
    

    
lemma_auto void array_inv<t>();
    requires [?f]array<t>(?a, ?n, ?size, ?q, ?elems);
    ensures [f]array<t>(a, n, size, q, elems) &*& 0 <= n &*& length(elems) == n;

predicate character(char *p; char c);
predicate u_character(unsigned char *p; unsigned char c);

predicate integer(int *p; int v);
predicate u_integer(unsigned int *p; unsigned int v);

predicate pointer(void **pp; void *p);

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
    ensures [f]pointer(pp, p) &*& true == ((void *)0 <= pp) &*& pp + sizeof(void *) <= (void *)UINTPTR_MAX;

fixpoint void *pointer_of_chars(list<char> cs);
fixpoint list<char> chars_of_pointer(void * p);
fixpoint bool chars_within_limits(list<char> cs);

lemma_auto(pointer_of_chars(chars_of_pointer(p))) void pointer_of_chars_of_pointer(void *p);
    requires p >= (void *)0 && p <= (void *)UINTPTR_MAX;
    ensures pointer_of_chars(chars_of_pointer(p)) == p && chars_within_limits(chars_of_pointer(p)) == true && length(chars_of_pointer(p)) == sizeof(void *);

lemma_auto(chars_of_pointer(pointer_of_chars(cs))) void chars_of_pointer_of_chars(list<char> cs);
    requires length(cs) == sizeof(void *) && chars_within_limits(cs) == true;
    ensures chars_of_pointer(pointer_of_chars(cs)) == cs;

@*/

/*@

predicate chars(char *array, int count; list<char> cs) =
    count == 0 ?
        cs == nil
    :
        character(array, ?c) &*& chars(array + 1, count - 1, ?cs0) &*& cs == cons(c, cs0);

lemma_auto void chars_inv();
    requires [?f]chars(?array, ?count, ?cs);
    ensures [f]chars(array, count, cs) &*& length(cs) == count;

lemma void chars_zero(); // There is nothing at address 0.
    requires [?f]chars(0, _, ?cs);
    ensures cs == nil;

lemma void char_limits(char *pc);
    requires [?f]character(pc, ?c);
    ensures [f]character(pc, c) &*& true == ((char *)0 <= pc) &*& pc < (char *)UINTPTR_MAX &*& -128 <= c &*& c <= 127;

lemma void chars_limits(char *array);
    requires [?f]chars(array, ?n, ?cs) &*& true == ((char *)0 <= array) &*& array <= (char *)UINTPTR_MAX;
    ensures [f]chars(array, n, cs) &*& true == ((char *)0 <= array) &*& array + n <= (char *)UINTPTR_MAX;

lemma void chars_split(char *array, int offset);
   requires [?f]chars(array, ?n, ?cs) &*& 0 <= offset &*& offset <= n;
   ensures
       [f]chars(array, offset, take(offset, cs))
       &*& [f]chars(array + offset, n - offset, drop(offset, cs))
       &*& append(take(offset, cs), drop(offset, cs)) == cs;

lemma void chars_join(char *array);
    requires [?f]chars(array, ?n, ?cs) &*& [f]chars(array + n, ?n0, ?cs0);
    ensures [f]chars(array, n + n0, append(cs, cs0));

// chars to ...
lemma void chars_to_integer(void *p);
    requires [?f]chars(p, sizeof(int), ?cs);
    ensures [f]integer(p, _);

lemma void chars_to_u_integer(void *p);
    requires [?f]chars(p, sizeof(unsigned int), ?cs);
    ensures [f]u_integer(p, _);

lemma void chars_to_pointer(void *p);
    requires [?f]chars(p, sizeof(void *), ?cs);
    ensures [f]pointer(p, pointer_of_chars(cs));

// ... to chars
lemma void integer_to_chars(void *p);
    requires [?f]integer(p, _);
    ensures [f]chars(p, sizeof(int), ?cs);

lemma void u_integer_to_chars(void *p);
    requires [?f]u_integer(p, _);
    ensures [f]chars(p, sizeof(unsigned int), ?cs);

lemma void pointer_to_chars(void *p);
    requires [?f]pointer(p, ?v);
    ensures [f]chars(p, sizeof(void *), chars_of_pointer(v));

// u_character to/from character
lemma void u_character_to_character(void *p);
    requires [?f]u_character(p, _);
    ensures [f]character(p, _);

lemma void character_to_u_character(void *p);
    requires [?f]character(p, _);
    ensures [f]u_character(p, _);

@*/

/*@

predicate string(char *s; list<char> cs) =
    character(s, ?c) &*&
    c == 0 ?
        cs == nil
    :
        string(s + 1, ?cs0) &*& cs == cons(c, cs0);

lemma void string_to_body_chars(char *s);
    requires [?f]string(s, ?cs);
    ensures [f]chars(s, _, cs) &*& [f]character(s + length(cs), 0) &*& !mem('\0', cs);

lemma void body_chars_to_string(char *s);
    requires [?f]chars(s, _, ?cs) &*& [f]character(s + length(cs), 0) &*& !mem('\0', cs);
    ensures [f]string(s, cs);

lemma void chars_to_string(char *s);
    requires [?f]chars(s, ?n, ?cs) &*& index_of('\0', cs) == n - 1;
    ensures [f]string(s, take(n - 1, cs));

lemma void string_to_chars(char *s);
    requires [?f]string(s, ?cs);
    ensures [f]chars(s, _, append(cs, cons('\0', nil))) &*& !mem('\0', cs);

lemma void chars_separate_string(char *s);
    requires [?f]chars(s, ?n, ?cs) &*& mem('\0', cs) == true;
    ensures [f]string(s, take(index_of('\0', cs), cs)) &*& [f]chars(s + index_of('\0', cs) + 1, n - index_of('\0', cs) - 1, drop(index_of('\0', cs) + 1, cs));

lemma void chars_unseparate_string(char *s);
    requires [?f]string(s, ?cs) &*& [f]chars(s + length(cs) + 1, ?n, ?cs1);
    ensures [f]chars(s, length(cs) + 1 + n, append(cs, cons('\0', cs1)));

lemma void string_limits(char *s);
    requires [?f]string(s, ?cs);
    ensures [f]string(s, cs) &*& true == ((char *)0 < s) &*& s + length(cs) < (char *)UINTPTR_MAX;

@*/

/*@

predicate module(int moduleId, bool initialState);
predicate module_code(int moduleId;);

predicate argv(char **argv, int argc) =
    argc <= 0 ? true : pointer(argv, ?arg) &*& string(arg, _) &*& argv(argv + 1, argc - 1);

@*/

typedef int main(int argc, char **argv);
    //@ requires 0 <= argc &*& [_]argv(argv, argc);
    //@ ensures true;

typedef int main_full/*@(int mainModule)@*/(int argc, char **argv);
    //@ requires module(mainModule, true) &*& [_]argv(argv, argc);
    //@ ensures true;

#endif
