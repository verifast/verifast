#ifndef STDARG_H
#define STDARG_H

//@ abstract_type __va_list;

typedef __va_list va_list;

//@ fixpoint int va_list_id(va_list ap);

//@ predicate va_list(va_list ap, void *lastParam, real frac, list<vararg> args);

void __va_start(va_list *app, void *lastParam);
//@ requires [?f]varargs_(lastParam, ?args) &*& *app |-> _;
//@ ensures [f/2]varargs_(lastParam, args) &*& *app |-> ?ap &*& va_list(ap, lastParam, f/2, args);
//@ terminates;

#define va_start(ap, lastParam) __va_start(&ap, &lastParam);

void va_end(va_list ap);
//@ requires [?f1]varargs_(?lastParam, ?args) &*& va_list(?ap1, lastParam, ?f2, _) &*& va_list_id(ap1) == va_list_id(ap);
//@ ensures [f1 + f2]varargs_(lastParam, args);
//@ terminates;

int __va_arg_int(va_list *app);
//@ requires *app |-> ?ap0 &*& va_list(ap0, ?lastParam, ?f, cons(vararg_int(sizeof(int), ?k), ?args));
//@ ensures *app |-> ?ap1 &*& va_list(ap1, lastParam, f, args) &*& result == k &*& va_list_id(ap1) == va_list_id(ap0);
//@ terminates;

unsigned int __va_arg_uint(va_list *app);
//@ requires *app |-> ?ap0 &*& va_list(ap0, ?lastParam, ?f, cons(vararg_uint(sizeof(unsigned int), ?k), ?args));
//@ ensures *app |-> ?ap1 &*& va_list(ap1, lastParam, f, args) &*& result == k &*& va_list_id(ap1) == va_list_id(ap0);
//@ terminates;

void *__va_arg_pointer(va_list *app);
//@ requires *app |-> ?ap0 &*& va_list(ap0, ?lastParam, ?f, cons(vararg_pointer(?p), ?args));
//@ ensures *app |-> ?ap1 &*& va_list(ap1, lastParam, f, args) &*& result == p &*& va_list_id(ap1) == va_list_id(ap0);
//@ terminates;

double __va_arg_double(va_list *app);
//@ requires *app |-> ?ap0 &*& va_list(ap0, ?lastParam, ?f, cons(vararg_double(?d), ?args));
//@ ensures *app |-> ?ap1 &*& va_list(ap1, lastParam, f, args) &*& result == d &*& va_list_id(ap1) == va_list_id(ap0);
//@ terminates;

#define va_arg(ap, type) _Generic((type)0, int: __va_arg_int(&ap), unsigned: __va_arg_uint(&ap), void *: __va_arg_pointer(&ap), double: __va_arg_double(&ap))

void __va_copy(va_list *dest, va_list src);
//@ requires *dest |-> _ &*& va_list(src, ?lastParam, ?f, ?args);
//@ ensures *dest |-> ?ap &*& va_list(src, lastParam, f/2, args) &*& va_list(ap, lastParam, f/2, args);
//@ terminates;

#define va_copy(dest, src) __va_copy(&dest, src)

#endif
