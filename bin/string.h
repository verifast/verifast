#ifndef STRING_H
#define STRING_H

void memcpy(void *array, void *array0, int count);
    //@ requires chars(array, ?cs) &*& [?f]chars(array0, ?cs0) &*& count == length(cs) &*& count == length(cs0);
    //@ ensures chars(array, cs0) &*& [f]chars(array0, cs0);

int strlen(char *string);
    //@ requires [?f]chars(string, ?cs) &*& mem('\0', cs) == true;
    //@ ensures [f]chars(string, cs) &*& result == index_of('\0', cs);

int memcmp(char *array, char *array0, int count);
    //@ requires [?f]chars(array, ?cs) &*& [?f0]chars(array0, ?cs0) &*& count == length(cs) &*& count == length(cs0);
    //@ ensures [f]chars(array, cs) &*& [f0]chars(array0, cs0) &*& true == ((result == 0) == (cs == cs0));

int strcmp(char *s1, char *s2);
    //@ requires [?f1]chars(s1, ?cs1) &*& mem('\0', cs1) == true &*& [?f2]chars(s2, ?cs2) &*& mem('\0', cs2) == true;
    //@ ensures [f1]chars(s1, cs1) &*& [f2]chars(s2, cs2);

char *memchr(char *array, char c, int count);
    //@ requires [?f]chars(array, ?cs) &*& length(cs) == count;
    //@ ensures [f]chars(array, cs) &*& result == 0 ? mem(c, cs) == false : mem(c, cs) == true &*& result == array + index_of(c, cs);

void memset(void *array, char value, int size);
    //@ requires chars(array, ?cs) &*& length(cs) == size;
    //@ ensures chars(array, ?cs1) &*& length(cs1) == size &*& all_eq(cs1, value) == true;

#endif