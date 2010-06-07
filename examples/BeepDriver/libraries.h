#ifndef LIBRARIES_H
#define LIBRARIES_H

struct library;

//@ predicate library(struct library *library, int mainModule);

struct library *load_library(char *name);
    //@ requires [?f]chars(name, ?nameChars) &*& mem('\0', nameChars) == true;
    //@ ensures [f]chars(name, nameChars) &*& result == 0 ? true : library(result, ?mainModule) &*& module(mainModule, true);

void *library_lookup_symbol(struct library *library, char *symbol);
    //@ requires [?f1]library(library, ?mainModule) &*& [?f2]chars(symbol, ?symbolChars) &*& mem('\0', symbolChars) == true;
    //@ ensures [f1]library(library, mainModule) &*& [f2]chars(symbol, symbolChars);

void library_free(struct library *library);
    //@ requires library(library, ?mainModule) &*& module(mainModule, false);
    //@ ensures true;

#endif