#ifndef STDARG_H
#define STDARG_H

typedef void *va_list;

//@ predicate va_list(va_list ap, void *lastParam, real frac, list<vararg> args);

void __va_start(va_list *app, void *lastParam);
//@ requires [?f]varargs_(lastParam, ?args) &*& *app |-> _;
//@ ensures [f/2]varargs_(lastParam, args) &*& *app |-> ?ap &*& va_list(ap, lastParam, f/2, args);

#define va_start(ap, lastParam) __va_start(&ap, &lastParam);

void va_end(va_list ap);
//@ requires [?f1]varargs_(?lastParam, ?args) &*& va_list(ap, lastParam, ?f2, _);
//@ ensures [f1 + f2]varargs_(lastParam, args);

int __va_arg_int(va_list *app);
//@ requires *app |-> ?ap0 &*& va_list(ap0, ?lastParam, ?f, cons(vararg_int(?k), ?args));
//@ ensures *app |-> ?ap1 &*& va_list(ap1, lastParam, f, args) &*& result == k;

unsigned int __va_arg_uint(va_list *app);
//@ requires *app |-> ?ap0 &*& va_list(ap0, ?lastParam, ?f, cons(vararg_uint(?k), ?args));
//@ ensures *app |-> ?ap1 &*& va_list(ap1, lastParam, f, args) &*& result == k;

void *__va_arg_pointer(va_list *app);
//@ requires *app |-> ?ap0 &*& va_list(ap0, ?lastParam, ?f, cons(vararg_pointer(?p), ?args));
//@ ensures *app |-> ?ap1 &*& va_list(ap1, lastParam, f, args) &*& result == p;

#define va_arg(ap, type) _Generic((type)0, int: __va_arg_int(&ap), unsigned: __va_arg_uint(&ap), void *: __va_arg_pointer(&ap))

void __va_copy(va_list *dest, va_list src);
//@ requires *dest |-> _ &*& va_list(src, ?lastParam, ?f, ?args);
//@ ensures *dest |-> ?ap &*& va_list(src, lastParam, f/2, args) &*& va_list(ap, lastParam, f/2, args);

#define va_copy(dest, src) __va_copy(&dest, src)

#endif
