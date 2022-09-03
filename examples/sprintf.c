#include <stdio.h>
#include <stdlib.h>

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    char* buffer =  malloc(50 * sizeof(char));
    if (buffer == 0) {abort();}
    
    sprintf(buffer, "Hello world");
    //@ assert [_]chars(buffer, 12, ?cs1);
    //@ assert cs1 == {'H', 'e', 'l', 'l', 'o', ' ', 'w', 'o', 'r', 'l', 'd', 0};
    //@ chars_chars__join(buffer);
    
    sprintf(buffer, "Hello %s", "universe");
    //@ assert [_]chars(buffer, 15, ?cs2);
    //@ assert cs2 == {'H', 'e', 'l', 'l', 'o', ' ', 'u', 'n', 'i', 'v', 'e', 'r', 's', 'e', 0};
    //@ chars_chars__join(buffer);
    
    sprintf(buffer, "%s %s %s", "aa", "bbbb", "cccccc");
    //@ assert [_]chars(buffer, 15, ?cs3);
    //@ assert cs3 == {'a', 'a', ' ', 'b', 'b', 'b', 'b', ' ', 'c', 'c', 'c', 'c', 'c', 'c', 0};
    //@ chars_chars__join(buffer);
    
    sprintf(buffer, "%s %s %s %s", "a", "b", "c", "d");
    //@ assert [_]chars(buffer, 8, ?cs4);
    //@ assert cs4 == {'a', ' ', 'b', ' ', 'c', ' ', 'd', 0};
    //@ chars_chars__join(buffer);

    sprintf(buffer, "%u", (unsigned int) 7);
    //@ assert [_]chars(buffer, 2, ?cs5);
    //@ assert cs5 == {'7', 0};
    //@ chars_chars__join(buffer);
    
    sprintf(buffer, "%i", 5);
    //@ assert [_]chars(buffer, 2, ?cs6);
    //@ assert cs6 == {'5', 0};
    //@ chars_chars__join(buffer);
    
    sprintf(buffer, "%i", -3);
    //@ assert [_]chars(buffer, 3, ?cs7);
    //@ assert cs7 == {'-', '3', 0};
    //@ chars_chars__join(buffer);
    
    sprintf(buffer, "%i%i%i%i", 1, 2, 3, 4);
    //@ assert [_]chars(buffer, 5, ?cs8);
    //@ assert cs8 == {'1', '2', '3', '4', 0};
    //@ chars_chars__join(buffer);
    
    free(buffer);
    
    return 0;
}