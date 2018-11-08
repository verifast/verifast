#ifndef JAYANTI_H
#define JAYANTI_H

// By Bart Jacobs
// Algorithm by Jayanti, as quoted in Delbianco, Sergey, Nanevski, and Banerjee, "Concurrent data structures linked in time", ECOOP 2017.

struct array;
typedef struct array *array_t;

/*@

predicate array_scanner(array_t array; predicate(int, int) inv);
predicate array_x_writer(array_t array; predicate(int, int) inv);
predicate array_y_writer(array_t array; predicate(int, int) inv);

@*/

array_t create_array();
    //@ requires exists<predicate(int, int)>(?inv) &*& inv(0, 0);
    //@ ensures array_scanner(result, inv) &*& array_x_writer(result, inv) &*& array_y_writer(result, inv);

/*@

typedef lemma void array_write_x_ghop(predicate(int, int) inv, int value, predicate() pre, predicate() post)();
    requires inv(?x, ?y) &*& pre();
    ensures inv(value, y) &*& post();

@*/

void array_write_x(array_t array, int value);
    /*@
    requires
        array_x_writer(array, ?inv) &*& value != INT_MIN &*&
        is_array_write_x_ghop(?ghop, inv, value, ?pre, ?post) &*& pre();
    @*/
    //@ ensures array_x_writer(array, inv) &*& post();

/*@

typedef lemma void array_write_y_ghop(predicate(int, int) inv, int value, predicate() pre, predicate() post)();
    requires inv(?x, ?y) &*& pre();
    ensures inv(x, value) &*& post();

@*/

void array_write_y(array_t array, int value);
    /*@
    requires
        array_y_writer(array, ?inv) &*& value != INT_MIN &*&
        is_array_write_y_ghop(?ghop, inv, value, ?pre, ?post) &*& pre();
    @*/
    //@ ensures array_y_writer(array, inv) &*& post();

/*@

typedef lemma void array_scan_ghop(predicate(int, int) inv, predicate() pre, predicate(int, int) post)();
    requires inv(?x, ?y) &*& pre();
    ensures inv(x, y) &*& post(x, y);

@*/

void array_scan(array_t array, int *x, int *y);
    /*@
    requires
        array_scanner(array, ?inv) &*& *x |-> _ &*& *y |-> _ &*&
        is_array_scan_ghop(?ghop, inv, ?pre, ?post) &*& pre();
    @*/
    //@ ensures array_scanner(array, inv) &*& *x |-> ?vx &*& *y |-> ?vy &*& post(vx, vy);

#endif
