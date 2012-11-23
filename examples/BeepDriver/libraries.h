#ifndef LIBRARIES_H
#define LIBRARIES_H

struct library;

//@ predicate library(struct library *library, int mainModule);

struct library *load_library(char *name);
    //@ requires [?f]string(name, ?nameChars);
    //@ ensures [f]string(name, nameChars) &*& result == 0 ? true : library(result, ?mainModule) &*& module(mainModule, true);

void *library_lookup_symbol(struct library *library, char *symbol);
    //@ requires [?f1]library(library, ?mainModule) &*& [?f2]chars(symbol, ?symbolLength, ?symbolChars) &*& mem('\0', symbolChars) == true;
    //@ ensures [f1]library(library, mainModule) &*& [f2]chars(symbol, symbolLength, symbolChars);

void library_free(struct library *library);
    //@ requires library(library, ?mainModule) &*& module(mainModule, false);
    //@ ensures true;

#endif