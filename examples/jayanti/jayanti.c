#include <stdlib.h>
#include "jayanti.h"
#include "atomics.h"

// By Bart Jacobs
// Algorithm by Jayanti, as quoted in Delbianco, Sergey, Nanevski, and Banerjee, "Concurrent data structures linked in time", ECOOP 2017.

struct array {
    int S;
    int_tracker Sid;
    int x;
    int_tracker xid;
    int fx;
    int_tracker fxid;
    int y;
    int_tracker yid;
    int fy;
    int_tracker fyid;
    
    //@ predicate(int, int) inv;
    
    //@ int scan_x_state; // 1 = between setting fx := _|_ and reading x; 2 = between reading x and setting S := false; 3 = between setting S := false and reading fx; 0 = elsewhere
    //@ int scanner_x;
    //@ int scanner_rx;
    //@ int scan_y_state;
    //@ int scanner_y;
    //@ int scanner_ry;

    //@ int write_x_state; // 1 = between writing x and reading S; 2 = between reading S and writing fx; 0 = elsewhere
    //@ int write_x_scan_cycle; // = S_nbWrites at time of 'p := x'
    //@ int write_x_read_S_nbWrites;
    //@ prophecy_id write_x_read_S_prophecy_id;
    //@ int write_x_write_fx_nbReads;
    //@ prophecy_id write_x_write_fx_prophecy_id;
    //@ int write_x_delayed_state; // 0 = not delayed; 1 = misses S; 2 = misses fx
    //@ predicate() write_x_post;
    
    //@ int write_y_state;
    //@ int write_y_scan_cycle;
    //@ int write_y_read_S_nbWrites;
    //@ prophecy_id write_y_read_S_prophecy_id;
    //@ int write_y_write_fy_nbReads;
    //@ prophecy_id write_y_write_fy_prophecy_id;
    //@ int write_y_delayed_state;
    //@ predicate() write_y_post;
};

/*@

predicate_ctor atomic_space_inv(struct array *array)() =
    [_]array->inv |-> ?inv &*&
    inv(?x_abstract_value, ?y_abstract_value) &*&
    
    [_]array->Sid |-> ?Sid &*& [1/2]tracked_int(Sid, &array->S, ?S, ?S_nbWrites) &*& tracked_int_reads_tracker(Sid, ?S_nbReads) &*&
    [_]array->xid |-> ?xid &*& [1/2]tracked_int(xid, &array->x, ?x, ?x_nbWrites) &*& [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*& x != INT_MIN &*&
    [_]array->fxid |-> ?fxid &*& tracked_int(fxid, &array->fx, ?fx, ?fx_nbWrites) &*& [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
    [_]array->yid |-> ?yid &*& [1/2]tracked_int(yid, &array->y, ?y, ?y_nbWrites) &*& [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*& y != INT_MIN &*&
    [_]array->fyid |-> ?fyid &*& tracked_int(fyid, &array->fy, ?fy, ?fy_nbWrites) &*& [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
    
    [1/2]array->scan_x_state |-> ?scan_x_state &*&
    [1/2]array->scanner_x |-> ?scanner_x &*&
    [1/2]array->scanner_rx |-> ?scanner_rx &*&
    [1/2]array->scan_y_state |-> ?scan_y_state &*&
    [1/2]array->scanner_y |-> ?scanner_y &*&
    [1/2]array->scanner_ry |-> ?scanner_ry &*&
    scan_x_state != 1 && scan_x_state != 2 || S == 1 &*&
    scan_y_state != 1 && scan_y_state != 2 || S == 1 &*&
    scan_x_state != 3 || S == 0 &*&
    scan_y_state != 3 || S == 0 &*&
    
    [1/2]array->write_x_state |-> ?write_x_state &*&
    [1/2]array->write_x_scan_cycle |-> ?write_x_scan_cycle &*&
    [1/2]array->write_x_read_S_nbWrites |-> ?write_x_read_S_nbWrites &*&
    [1/2]array->write_x_read_S_prophecy_id |-> ?write_x_read_S_prophecy_id &*&
    (write_x_state == 1 ? [1/2]prophecy(write_x_read_S_prophecy_id, Sid, ?write_x_S, write_x_read_S_nbWrites, ?write_x_read_S_nbReads) : true) &*&
    [1/2]array->write_x_write_fx_nbReads |-> ?write_x_write_fx_nbReads &*&
    [1/2]array->write_x_write_fx_prophecy_id |-> ?write_x_write_fx_prophecy_id &*&
    (write_x_state == 2 ? [1/2]prophecy(write_x_write_fx_prophecy_id, fxid, ?write_x_fx, ?write_x_write_fx_nbWrites, write_x_write_fx_nbReads) : true) &*&
    [1/2]array->write_x_delayed_state |-> ?write_x_delayed_state &*&
    [1/2]array->write_x_post |-> ?write_x_post &*&
    (write_x_delayed_state != 0 ?
         write_x_delayed_state == 1 || write_x_delayed_state == 2 &*&
         write_x_state != 0 &*&
         write_x_delayed_state == 1 || (S_nbWrites >= write_x_read_S_nbWrites && (S_nbWrites > write_x_read_S_nbWrites || S == 1)) &*&
         S_nbWrites == write_x_scan_cycle ?
             (scan_x_state == 1 || scan_x_state == 2) &*&
             write_x_delayed_state != 1 || S_nbWrites < write_x_read_S_nbWrites &*&
             write_x_delayed_state != 2 || fx_nbReads < write_x_write_fx_nbReads &*&
             is_array_write_x_ghop(?ghop, inv, x, ?pre, write_x_post) &*& pre()
         :
             S_nbWrites > write_x_scan_cycle &*&
             write_x_post()
     :
         true
    ) &*&
    write_x_state == 0 || write_x_scan_cycle <= S_nbWrites &*&
    scan_x_state != 3 || write_x_state != 2 || write_x_scan_cycle < S_nbWrites &*&
    write_x_state != 0 || scan_x_state != 1 && scan_x_state != 2 || fx == INT_MIN || fx == x &*&
    write_x_state != 0 || scan_x_state != 2 || fx == x || scanner_x == x &*&
    write_x_state == 0 || write_x_state == 1 || write_x_state == 2 &*&
    scan_x_state != 3 || write_x_delayed_state != 2 || write_x_scan_cycle != S_nbWrites - 1 || write_x_state != 2 || fx_nbReads < write_x_write_fx_nbReads &*&
    scan_x_state != 1 || write_x_delayed_state != 0 || write_x_scan_cycle != S_nbWrites || write_x_state != 1 && write_x_state != 2 || fx == INT_MIN || fx_nbReads >= write_x_write_fx_nbReads &*&
    scan_x_state != 2 || write_x_delayed_state != 0 || write_x_scan_cycle != S_nbWrites || write_x_state != 1 && write_x_state != 2 || fx == INT_MIN && scanner_x == x || fx_nbReads >= write_x_write_fx_nbReads &*&
    scan_x_state != 3 || write_x_delayed_state != 0 || write_x_scan_cycle != S_nbWrites - 1 || write_x_state != 2 || scanner_rx == x && (fx_nbReads >= write_x_write_fx_nbReads || fx == INT_MIN && scanner_x == x) &*&
    scan_x_state != 1 || write_x_scan_cycle >= S_nbWrites || write_x_state != 1 && write_x_state != 2 || fx == INT_MIN &*&
    scan_x_state != 2 || write_x_scan_cycle >= S_nbWrites || write_x_state != 1 && write_x_state != 2 || scanner_x == x && fx == INT_MIN &*&
    scan_x_state != 3 || write_x_scan_cycle >= S_nbWrites - 1 || write_x_state != 2 || scanner_x == x && scanner_rx == x && fx == INT_MIN &*&
    scan_x_state != 1 || write_x_delayed_state != 0 && write_x_scan_cycle == S_nbWrites || write_x_state != 1 || write_x_read_S_nbWrites <= S_nbWrites || fx == INT_MIN &*&
    scan_x_state != 2 || write_x_delayed_state != 0 && write_x_scan_cycle == S_nbWrites || write_x_state != 1 || write_x_read_S_nbWrites <= S_nbWrites || x == scanner_x && fx == INT_MIN &*&
    scan_x_state != 3 || write_x_state == 2 || scanner_rx == (fx == INT_MIN ? scanner_x : fx) &*&
    scan_x_state != 3 || write_x_delayed_state == 0 || write_x_scan_cycle != S_nbWrites - 1 || scanner_rx == (fx == INT_MIN ? scanner_x : fx) &*&
    (write_x_delayed_state != 0 && S_nbWrites == write_x_scan_cycle ?
         x_abstract_value == (fx != INT_MIN ? fx : scanner_x)
     :
         x_abstract_value == x
    ) &*&
    
    [1/2]array->write_y_state |-> ?write_y_state &*&
    [1/2]array->write_y_scan_cycle |-> ?write_y_scan_cycle &*&
    [1/2]array->write_y_read_S_nbWrites |-> ?write_y_read_S_nbWrites &*&
    [1/2]array->write_y_read_S_prophecy_id |-> ?write_y_read_S_prophecy_id &*&
    (write_y_state == 1 ? [1/2]prophecy(write_y_read_S_prophecy_id, Sid, ?write_y_S, write_y_read_S_nbWrites, ?write_y_read_S_nbReads) : true) &*&
    [1/2]array->write_y_write_fy_nbReads |-> ?write_y_write_fy_nbReads &*&
    [1/2]array->write_y_write_fy_prophecy_id |-> ?write_y_write_fy_prophecy_id &*&
    (write_y_state == 2 ? [1/2]prophecy(write_y_write_fy_prophecy_id, fyid, ?write_y_fy, ?write_y_write_fy_nbWrites, write_y_write_fy_nbReads) : true) &*&
    [1/2]array->write_y_delayed_state |-> ?write_y_delayed_state &*&
    [1/2]array->write_y_post |-> ?write_y_post &*&
    (write_y_delayed_state != 0 ?
         write_y_delayed_state == 1 || write_y_delayed_state == 2 &*&
         write_y_state != 0 &*&
         write_y_delayed_state == 1 || (S_nbWrites >= write_y_read_S_nbWrites && (S_nbWrites > write_y_read_S_nbWrites || S == 1)) &*&
         S_nbWrites == write_y_scan_cycle ?
             (scan_y_state == 1 || scan_y_state == 2) &*&
             write_y_delayed_state != 1 || S_nbWrites < write_y_read_S_nbWrites &*&
             write_y_delayed_state != 2 || fy_nbReads < write_y_write_fy_nbReads &*&
             is_array_write_y_ghop(?ghop, inv, y, ?pre, write_y_post) &*& pre()
         :
             S_nbWrites > write_y_scan_cycle &*&
             write_y_post()
     :
         true
    ) &*&
    write_y_state == 0 || write_y_scan_cycle <= S_nbWrites &*&
    scan_y_state != 3 || write_y_state != 2 || write_y_scan_cycle < S_nbWrites &*&
    write_y_state != 0 || scan_y_state != 1 && scan_y_state != 2 || fy == INT_MIN || fy == y &*&
    write_y_state != 0 || scan_y_state != 2 || fy == y || scanner_y == y &*&
    write_y_state == 0 || write_y_state == 1 || write_y_state == 2 &*&
    scan_y_state != 3 || write_y_delayed_state != 2 || write_y_scan_cycle != S_nbWrites - 1 || write_y_state != 2 || fy_nbReads < write_y_write_fy_nbReads &*&
    scan_y_state != 1 || write_y_delayed_state != 0 || write_y_scan_cycle != S_nbWrites || write_y_state != 1 && write_y_state != 2 || fy == INT_MIN || fy_nbReads >= write_y_write_fy_nbReads &*&
    scan_y_state != 2 || write_y_delayed_state != 0 || write_y_scan_cycle != S_nbWrites || write_y_state != 1 && write_y_state != 2 || fy == INT_MIN && scanner_y == y || fy_nbReads >= write_y_write_fy_nbReads &*&
    scan_y_state != 3 || write_y_delayed_state != 0 || write_y_scan_cycle != S_nbWrites - 1 || write_y_state != 2 || scanner_ry == y && (fy_nbReads >= write_y_write_fy_nbReads || fy == INT_MIN && scanner_y == y) &*&
    scan_y_state != 1 || write_y_scan_cycle >= S_nbWrites || write_y_state != 1 && write_y_state != 2 || fy == INT_MIN &*&
    scan_y_state != 2 || write_y_scan_cycle >= S_nbWrites || write_y_state != 1 && write_y_state != 2 || scanner_y == y && fy == INT_MIN &*&
    scan_y_state != 3 || write_y_scan_cycle >= S_nbWrites - 1 || write_y_state != 2 || scanner_y == y && scanner_ry == y && fy == INT_MIN &*&
    scan_y_state != 1 || write_y_delayed_state != 0 && write_y_scan_cycle == S_nbWrites || write_y_state != 1 || write_y_read_S_nbWrites <= S_nbWrites || fy == INT_MIN &*&
    scan_y_state != 2 || write_y_delayed_state != 0 && write_y_scan_cycle == S_nbWrites || write_y_state != 1 || write_y_read_S_nbWrites <= S_nbWrites || y == scanner_y && fy == INT_MIN &*&
    scan_y_state != 3 || write_y_state == 2 || scanner_ry == (fy == INT_MIN ? scanner_y : fy) &*&
    scan_y_state != 3 || write_y_delayed_state == 0 || write_y_scan_cycle != S_nbWrites - 1 || scanner_ry == (fy == INT_MIN ? scanner_y : fy) &*&
    (write_y_delayed_state != 0 && S_nbWrites == write_y_scan_cycle ?
         y_abstract_value == (fy != INT_MIN ? fy : scanner_y)
     :
         y_abstract_value == y
    );

predicate array_scanner(array_t array; predicate(int, int) inv) =
    [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
    [_]array->Sid |-> ?Sid &*& [_]is_tracked_int(Sid) &*&
    [_]array->xid |-> ?xid &*& [_]is_tracked_int(xid) &*&
    [_]array->fxid |-> ?fxid &*& [_]is_tracked_int(fxid) &*&
    [_]array->yid |-> ?yid &*& [_]is_tracked_int(yid) &*&
    [_]array->fyid |-> ?fyid &*& [_]is_tracked_int(fyid) &*&
    [1/2]tracked_int(Sid, &array->S, 0, ?S_nbWrites) &*&
    [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
    [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
    [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
    [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
    [1/2]array->scan_x_state |-> 0 &*&
    [1/2]array->scanner_x |-> _ &*&
    [1/2]array->scanner_rx |-> _ &*&
    [1/2]array->scan_y_state |-> 0 &*&
    [1/2]array->scanner_y |-> _ &*&
    [1/2]array->scanner_ry |-> _ &*&
    [_]array->inv |-> inv;

predicate array_x_writer(array_t array; predicate(int, int) inv) =
    [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
    [_]array->Sid |-> ?Sid &*& [_]is_tracked_int(Sid) &*&
    [_]array->xid |-> ?xid &*& [_]is_tracked_int(xid) &*&
    [_]array->fxid |-> ?fxid &*& [_]is_tracked_int(fxid) &*&
    [_]array->yid |-> ?yid &*& [_]is_tracked_int(yid) &*&
    [_]array->fyid |-> ?fyid &*& [_]is_tracked_int(fyid) &*&
    [1/2]tracked_int(xid, &array->x, _, ?x_nbWrites) &*&
    [1/2]array->write_x_state |-> 0 &*&
    [1/2]array->write_x_scan_cycle |-> _ &*&
    [1/2]array->write_x_delayed_state |-> 0 &*&
    [1/2]array->write_x_read_S_nbWrites |-> _ &*&
    [1/2]array->write_x_read_S_prophecy_id |-> _ &*&
    [1/2]array->write_x_write_fx_nbReads |-> _ &*&
    [1/2]array->write_x_write_fx_prophecy_id |-> _ &*&
    [1/2]array->write_x_post |-> _ &*&
    [_]array->inv |-> inv;

predicate array_y_writer(array_t array; predicate(int, int) inv) =
    [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
    [_]array->Sid |-> ?Sid &*& [_]is_tracked_int(Sid) &*&
    [_]array->xid |-> ?xid &*& [_]is_tracked_int(xid) &*&
    [_]array->fxid |-> ?fxid &*& [_]is_tracked_int(fxid) &*&
    [_]array->yid |-> ?yid &*& [_]is_tracked_int(yid) &*&
    [_]array->fyid |-> ?fyid &*& [_]is_tracked_int(fyid) &*&
    [1/2]tracked_int(yid, &array->y, _, ?y_nbWrites) &*&
    [1/2]array->write_y_state |-> 0 &*&
    [1/2]array->write_y_scan_cycle |-> _ &*&
    [1/2]array->write_y_delayed_state |-> 0 &*&
    [1/2]array->write_y_read_S_nbWrites |-> _ &*&
    [1/2]array->write_y_read_S_prophecy_id |-> _ &*&
    [1/2]array->write_y_write_fy_nbReads |-> _ &*&
    [1/2]array->write_y_write_fy_prophecy_id |-> _ &*&
    [1/2]array->write_y_post |-> _ &*&
    [_]array->inv |-> inv;

@*/

array_t create_array()
    //@ requires exists<predicate(int, int)>(?inv) &*& inv(0, 0);
    //@ ensures array_scanner(result, inv) &*& array_x_writer(result, inv) &*& array_y_writer(result, inv);
{
    //@ open exists(_);
    array_t array = malloc(sizeof(struct array));
    if (array == 0) abort();
    //@ leak malloc_block_array(array);
    array->S = 0;
    array->x = 0;
    array->fx = INT_MIN;
    array->y = 0;
    array->fy = INT_MIN;
    //@ array->inv = inv;
    array->Sid = start_tracking_int(&array->S);
    array->xid = start_tracking_int(&array->x);
    array->fxid = start_tracking_int(&array->fx);
    array->yid = start_tracking_int(&array->y);
    array->fyid = start_tracking_int(&array->fy);
    //@ leak array->inv |-> _ &*& array->Sid |-> _ &*& array->xid |-> _ &*& array->fxid |-> _ &*& array->yid |-> _ &*& array->fyid |-> _;
    //@ array->scan_x_state = 0;
    //@ array->scan_y_state = 0;
    //@ array->write_x_state = 0;
    //@ array->write_x_delayed_state = 0;
    //@ array->write_y_state = 0;
    //@ array->write_y_delayed_state = 0;
    //@ close atomic_space_inv(array)();
    //@ create_popl20_atomic_space(create_array, atomic_space_inv(array));
    //@ leak popl20_atomic_space(create_array, atomic_space_inv(array));
    return array;
}

void array_write_x(array_t array, int value)
    /*@
    requires
        array_x_writer(array, ?inv) &*& value != INT_MIN &*&
        is_array_write_x_ghop(?ghop, inv, value, ?pre, ?post) &*& pre();
    @*/
    //@ ensures array_x_writer(array, inv) &*& post();
{
    //@ open array_x_writer(array, inv);
    //@ int_tracker Sid = array->Sid;
    //@ int_tracker xid = array->xid;
    //@ int_tracker fxid = array->fxid;
    
    //@ close exists(array->xid);
    prophecy_id pidX = create_prophecy(array->xid);
    //@ assert prophecy(pidX, xid, ?prophecyX, ?prophecyXNbWrites, ?prophecyXNbReads);
    
    //@ close exists(array->Sid);
    prophecy_id pidS = create_prophecy(array->Sid);
    //@ assert prophecy(pidS, Sid, ?prophecyS, ?prophecySNbWrites, ?prophecySNbReads);
    
    //@ close exists(array->fxid);
    prophecy_id pidFX = create_prophecy(array->fxid);
    //@ assert prophecy(pidFX, fxid, ?prophecyFX, ?prophecyFXNbWrites, ?prophecyFXNbReads);

    {
        /*@
        predicate pre_() =
            [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
            [_]array->inv |-> inv &*&
            [_]array->Sid |-> Sid &*&
            [_]array->xid |-> xid &*&
            [_]array->fxid |-> fxid &*&
            [1/2]tracked_int(xid, &array->x, _, _) &*&
            [1/2]array->write_x_state |-> 0 &*&
            [1/2]array->write_x_scan_cycle |-> _ &*&
            [1/2]array->write_x_delayed_state |-> 0 &*&
            [1/2]array->write_x_read_S_nbWrites |-> _ &*&
            [1/2]array->write_x_read_S_prophecy_id |-> _ &*&
            [1/2]array->write_x_write_fx_nbReads |-> _ &*&
            [1/2]array->write_x_write_fx_prophecy_id |-> _ &*&
            [1/2]array->write_x_post |-> _ &*&
            [1/2]prophecy(pidS, Sid, prophecyS, prophecySNbWrites, prophecySNbReads) &*&
            is_array_write_x_ghop(ghop, inv, value, pre, post) &*& pre() &*&
            prophecy(pidX, xid, prophecyX, prophecyXNbWrites, prophecyXNbReads);
        predicate post_() =
            [1/2]tracked_int(xid, &array->x, value, _) &*&
            [1/2]array->write_x_state |-> 1 &*&
            [1/2]array->write_x_scan_cycle |-> _ &*&
            [1/2]array->write_x_delayed_state |-> ?delayedState &*&
            [1/2]array->write_x_read_S_nbWrites |-> prophecySNbWrites &*&
            [1/2]array->write_x_read_S_prophecy_id |-> pidS &*&
            [1/2]array->write_x_write_fx_nbReads |-> prophecyFXNbReads &*&
            [1/2]array->write_x_write_fx_prophecy_id |-> pidFX &*&
            [1/2]array->write_x_post |-> post &*&
            (delayedState != 0 ? true : post());
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_store_int_ghop(pidX, &array->x, value, pre_, post_)() {
            assert is_atomic_store_int_op(?op, _, _, _, ?P, ?Q);
            open pre_();
            popl20_open_atomic_space();
            open atomic_space_inv(array)();
            assert [_]tracked_int(Sid, &array->S, ?S, ?S_nbWrites);
            assert tracked_int(xid, &array->x, ?x, ?x_nbWrites);
            assert [_]tracked_int(fxid, &array->fx, ?fx, ?fx_nbWrites) &*& [_]tracked_int_reads_tracker(fxid, ?fx_nbReads);
            array->write_x_state = 1;
            array->write_x_scan_cycle = S_nbWrites;
            array->write_x_read_S_nbWrites = prophecySNbWrites;
            array->write_x_read_S_prophecy_id = pidS;
            array->write_x_write_fx_nbReads = prophecyFXNbReads;
            array->write_x_write_fx_prophecy_id = pidFX;
            array->write_x_post = post;
            if ((array->scan_x_state == 1 && fx != INT_MIN || array->scan_x_state == 2) && (prophecySNbWrites > S_nbWrites || prophecyFXNbReads > fx_nbReads)) {
                if (prophecySNbWrites > S_nbWrites)
                    array->write_x_delayed_state = 1;
                else
                    array->write_x_delayed_state = 2;
            } else {
                ghop();
                leak is_array_write_x_ghop(_, _, _, _, _);
            }
            produce_func_lt(atomic_store_int);
            assert func_lt(atomic_store_int, create_array) == true;
            op();
            close post_();
            close atomic_space_inv(array)();
            popl20_close_atomic_space();
        };
        @*/
        //@ close pre_();
        atomic_store_int(pidX, &array->x, value);
        //@ open post_();
    }
    //@ int write_x_scan_cycle = array->write_x_scan_cycle;
    //@ int delayedState = array->write_x_delayed_state;
    int write_x_S;
    {
        /*@
        predicate pre_() =
            [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
            [_]array->inv |-> inv &*&
            [_]array->Sid |-> Sid &*&
            [_]array->xid |-> xid &*&
            [_]array->fxid |-> fxid &*&
            [1/2]tracked_int(xid, &array->x, value, _) &*&
            [1/2]array->write_x_state |-> 1 &*&
            [1/2]array->write_x_scan_cycle |-> write_x_scan_cycle &*&
            [1/2]array->write_x_delayed_state |-> delayedState &*&
            [1/2]array->write_x_read_S_nbWrites |-> prophecySNbWrites &*&
            [1/2]array->write_x_read_S_prophecy_id |-> pidS &*&
            [1/2]array->write_x_write_fx_nbReads |-> prophecyFXNbReads &*&
            [1/2]array->write_x_write_fx_prophecy_id |-> pidFX &*&
            (prophecyS != 0 ? [1/2]prophecy(pidFX, fxid, prophecyFX, prophecyFXNbWrites, prophecyFXNbReads) : true) &*&
            [1/2]array->write_x_post |-> post &*&
            [1/2]prophecy(pidS, Sid, prophecyS, prophecySNbWrites, prophecySNbReads);
        predicate post_(int result) =
            result == prophecyS &*&
            [1/2]tracked_int(xid, &array->x, value, _) &*&
            [1/2]array->write_x_read_S_nbWrites |-> prophecySNbWrites &*&
            [1/2]array->write_x_read_S_prophecy_id |-> pidS &*&
            [1/2]array->write_x_write_fx_nbReads |-> prophecyFXNbReads &*&
            [1/2]array->write_x_write_fx_prophecy_id |-> pidFX &*&
            [1/2]array->write_x_scan_cycle |-> write_x_scan_cycle &*&
            [1/2]array->write_x_post |-> post &*&
            [1/2]array->write_x_state |-> (prophecyS == 0 ? 0 : 2) &*&
            delayedState == 1 ?
                [1/2]array->write_x_delayed_state |-> 0 &*& post()
            :
                [1/2]array->write_x_delayed_state |-> delayedState &*& delayedState == 0 || prophecyS != 0;
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_load_int_ghop(pidS, &array->S, pre_, post_)() {
            assert is_atomic_load_int_op(?op, _, _, ?P, ?Q);
            open pre_();
            popl20_open_atomic_space();
            open atomic_space_inv(array)();
            assert [_]tracked_int(Sid, &array->S, ?S, ?S_nbWrites);
            array->write_x_state = prophecyS == 0 ? 0 : 2;
            op();
            if (delayedState == 1)
                array->write_x_delayed_state = 0;
            close post_(prophecyS);
            close atomic_space_inv(array)();
            popl20_close_atomic_space();
        };
        @*/
        //@ close pre_();
        write_x_S = atomic_load_int(pidS, &array->S);
        //@ open post_(_);
    }
    //@ int newDelayedState = array->write_x_delayed_state;
    //@ assert newDelayedState != 1;
    if (write_x_S) {
        /*@
        predicate pre_() =
            [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
            [_]array->inv |-> inv &*&
            [_]array->Sid |-> Sid &*&
            [_]array->xid |-> xid &*&
            [_]array->fxid |-> fxid &*&
            [1/2]tracked_int(xid, &array->x, value, _) &*&
            [1/2]array->write_x_state |-> 2 &*&
            [1/2]array->write_x_scan_cycle |-> write_x_scan_cycle &*&
            [1/2]array->write_x_delayed_state |-> newDelayedState &*&
            [1/2]array->write_x_read_S_nbWrites |-> prophecySNbWrites &*&
            [1/2]array->write_x_write_fx_nbReads |-> prophecyFXNbReads &*&
            [1/2]array->write_x_write_fx_prophecy_id |-> pidFX &*&
            [1/2]array->write_x_post |-> post &*&
            [1/2]prophecy(pidFX, fxid, prophecyFX, prophecyFXNbWrites, prophecyFXNbReads);
        predicate post_() =
            [1/2]tracked_int(xid, &array->x, value, _) &*&
            [1/2]array->write_x_read_S_nbWrites |-> prophecySNbWrites &*&
            [1/2]array->write_x_write_fx_nbReads |-> prophecyFXNbReads &*&
            [1/2]array->write_x_write_fx_prophecy_id |-> pidFX &*&
            [1/2]array->write_x_scan_cycle |-> write_x_scan_cycle &*&
            [1/2]array->write_x_post |-> post &*&
            [1/2]array->write_x_state |-> 0 &*&
            [1/2]array->write_x_delayed_state |-> 0 &*&
            (newDelayedState != 0 ? post() : true);
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_store_int_ghop(pidFX, &array->fx, value, pre_, post_)() {
            assert is_atomic_store_int_op(?op, _, _, _, ?P, ?Q);
            open pre_();
            popl20_open_atomic_space();
            open atomic_space_inv(array)();
            array->write_x_state = 0;
            op();
            array->write_x_delayed_state = 0;
            assert [_]tracked_int(Sid, &array->S, ?S, ?S_nbWrites);
            if (array->scan_x_state == 3) {
                if (array->write_x_delayed_state != 0) {
                } else if (array->write_x_scan_cycle != S_nbWrites - 1) {
                    assert array->write_x_scan_cycle < S_nbWrites - 1;
                    assert array->scanner_rx == value;
                }
            }
            close post_();
            close atomic_space_inv(array)();
            popl20_close_atomic_space();
        };
        @*/
        //@ close pre_();
        atomic_store_int(pidFX, &array->fx, value);
        //@ open post_();
    }
    //@ if (!write_x_S) { leak prophecy(pidFX, _, _, _, _); } 
}

void array_scan(array_t array, int *px, int *py)
    /*@
    requires
        array_scanner(array, ?inv) &*& *px |-> _ &*& *py |-> _ &*&
        is_array_scan_ghop(?ghop, inv, ?pre, ?post) &*& pre();
    @*/
    //@ ensures array_scanner(array, inv) &*& *px |-> ?vx &*& *py |-> ?vy &*& post(vx, vy);
{
    //@ open array_scanner(array, inv);
    //@ int_tracker Sid = array->Sid;
    //@ int_tracker xid = array->xid;
    //@ int_tracker fxid = array->fxid;
    //@ int_tracker yid = array->yid;
    //@ int_tracker fyid = array->fyid;

    //@ close exists(Sid);
    prophecy_id pidS1 = create_prophecy(array->Sid);
    //@ assert prophecy(pidS1, Sid, ?prophecyS1, ?prophecyS1NbWrites, ?prophecyS1NbReads);
    
    prophecy_id pidFXbot = create_prophecy(array->fxid);
    //@ assert prophecy(pidFXbot, fxid, ?prophecyFXbot, ?prophecyFXbotNbWrites, ?prophecyFXbotNbReads);
    
    prophecy_id pidFYbot = create_prophecy(array->fyid);
    //@ assert prophecy(pidFYbot, fyid, ?prophecyFYbot, ?prophecyFYbotNbWrites, ?prophecyFYbotNbReads);
    
    prophecy_id pidX = create_prophecy(array->xid);
    //@ assert prophecy(pidX, xid, ?prophecyX, ?prophecyXNbWrites, ?prophecyXNbReads);
    
    prophecy_id pidY = create_prophecy(array->yid);
    //@ assert prophecy(pidY, yid, ?prophecyY, ?prophecyYNbWrites, ?prophecyYNbReads);
    
    prophecy_id pidS0 = create_prophecy(array->Sid);
    //@ assert prophecy(pidS0, Sid, ?prophecyS0, ?prophecyS0NbWrites, ?prophecyS0NbReads);
    
    prophecy_id pidFX = create_prophecy(array->fxid);
    //@ assert prophecy(pidFX, fxid, ?prophecyFX, ?prophecyFXNbWrites, ?prophecyFXNbReads);
    
    prophecy_id pidFY = create_prophecy(array->fyid);
    //@ assert prophecy(pidFY, fyid, ?prophecyFY, ?prophecyFYNbWrites, ?prophecyFYNbReads);

    {
        /*@
        predicate pre_() =
            [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
            [_]array->inv |-> inv &*&
            [_]array->Sid |-> Sid &*&
            [_]array->xid |-> xid &*&
            [_]array->fxid |-> fxid &*&
            [_]array->yid |-> yid &*&
            [_]array->fyid |-> fyid &*&
            [1/2]tracked_int(Sid, &array->S, 0, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 0 &*&
            [1/2]array->scanner_x |-> _ &*&
            [1/2]array->scan_y_state |-> 0 &*&
            [1/2]array->scanner_y |-> _ &*&
            prophecy(pidS1, Sid, prophecyS1, prophecyS1NbWrites, prophecyS1NbReads);
        predicate post_() =
            [1/2]tracked_int(Sid, &array->S, 1, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 0 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scan_y_state |-> 0 &*&
            [1/2]array->scanner_y |-> prophecyY;
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_store_int_ghop(pidS1, &array->S, 1, pre_, post_)() {
            assert is_atomic_store_int_op(?op, _, _, _, ?P, ?Q);
            open pre_();
            popl20_open_atomic_space();
            open atomic_space_inv(array)();
            produce_func_lt(atomic_store_int);
            op();
            array->scanner_x = prophecyX;
            array->scanner_y = prophecyY;
            close post_();
            close atomic_space_inv(array)();
            popl20_close_atomic_space();
        };
        @*/
        //@ close pre_();
        atomic_store_int(pidS1, &array->S, 1);
        //@ open post_();
    }
    {
        /*@
        predicate pre_() =
            [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
            [_]array->inv |-> inv &*&
            [_]array->Sid |-> Sid &*&
            [_]array->xid |-> xid &*&
            [_]array->fxid |-> fxid &*&
            [_]array->yid |-> yid &*&
            [_]array->fyid |-> fyid &*&
            [1/2]tracked_int(Sid, &array->S, 1, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 0 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scan_y_state |-> 0 &*&
            [1/2]array->scanner_y |-> prophecyY &*&
            prophecy(pidFXbot, fxid, prophecyFXbot, prophecyFXbotNbWrites, prophecyFXbotNbReads);
        predicate post_() =
            [1/2]tracked_int(Sid, &array->S, 1, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 1 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scan_y_state |-> 0 &*&
            [1/2]array->scanner_y |-> prophecyY;
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_store_int_ghop(pidFXbot, &array->fx, INT_MIN, pre_, post_)() {
            assert is_atomic_store_int_op(?op, _, _, _, ?P, ?Q);
            open pre_();
            popl20_open_atomic_space();
            open atomic_space_inv(array)();
            op();
            array->scan_x_state = 1;
            close post_();
            close atomic_space_inv(array)();
            popl20_close_atomic_space();
        };
        @*/
        //@ close pre_();
        atomic_store_int(pidFXbot, &array->fx, INT_MIN);
        //@ open post_();
    }
    {
        /*@
        predicate pre_() =
            [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
            [_]array->inv |-> inv &*&
            [_]array->Sid |-> Sid &*&
            [_]array->xid |-> xid &*&
            [_]array->fxid |-> fxid &*&
            [_]array->yid |-> yid &*&
            [_]array->fyid |-> fyid &*&
            [1/2]tracked_int(Sid, &array->S, 1, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 1 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scan_y_state |-> 0 &*&
            [1/2]array->scanner_y |-> prophecyY &*&
            prophecy(pidFYbot, fyid, prophecyFYbot, prophecyFYbotNbWrites, prophecyFYbotNbReads);
        predicate post_() =
            [1/2]tracked_int(Sid, &array->S, 1, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 1 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scan_y_state |-> 1 &*&
            [1/2]array->scanner_y |-> prophecyY;
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_store_int_ghop(pidFYbot, &array->fy, INT_MIN, pre_, post_)() {
            assert is_atomic_store_int_op(?op, _, _, _, ?P, ?Q);
            open pre_();
            popl20_open_atomic_space();
            open atomic_space_inv(array)();
            op();
            array->scan_y_state = 1;
            close post_();
            close atomic_space_inv(array)();
            popl20_close_atomic_space();
        };
        @*/
        //@ close pre_();
        atomic_store_int(pidFYbot, &array->fy, INT_MIN);
        //@ open post_();
    }
    int vx;
    {
        /*@
        predicate pre_() =
            [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
            [_]array->inv |-> inv &*&
            [_]array->Sid |-> Sid &*&
            [_]array->xid |-> xid &*&
            [_]array->fxid |-> fxid &*&
            [_]array->yid |-> yid &*&
            [_]array->fyid |-> fyid &*&
            [1/2]tracked_int(Sid, &array->S, 1, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 1 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scan_y_state |-> 1 &*&
            [1/2]array->scanner_y |-> prophecyY &*&
            prophecy(pidX, xid, prophecyX, prophecyXNbWrites, prophecyXNbReads);
        predicate post_(int result) =
            result == prophecyX &*&
            [1/2]tracked_int(Sid, &array->S, 1, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 2 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scan_y_state |-> 1 &*&
            [1/2]array->scanner_y |-> prophecyY;
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_load_int_ghop(pidX, &array->x, pre_, post_)() {
            assert is_atomic_load_int_op(?op, _, _, ?P, ?Q);
            open pre_();
            popl20_open_atomic_space();
            open atomic_space_inv(array)();
            op();
            array->scan_x_state = 2;
            close post_(prophecyX);
            close atomic_space_inv(array)();
            popl20_close_atomic_space();
        };
        @*/
        //@ close pre_();
        vx = atomic_load_int(pidX, &array->x);
        //@ open post_(_);
    }
    int vy;
    {
        /*@
        predicate pre_() =
            [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
            [_]array->inv |-> inv &*&
            [_]array->Sid |-> Sid &*&
            [_]array->xid |-> xid &*&
            [_]array->fxid |-> fxid &*&
            [_]array->yid |-> yid &*&
            [_]array->fyid |-> fyid &*&
            [1/2]tracked_int(Sid, &array->S, 1, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 2 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scan_y_state |-> 1 &*&
            [1/2]array->scanner_y |-> prophecyY &*&
            prophecy(pidY, yid, prophecyY, prophecyYNbWrites, prophecyYNbReads);
        predicate post_(int result) =
            result == prophecyY &*&
            [1/2]tracked_int(Sid, &array->S, 1, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 2 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scan_y_state |-> 2 &*&
            [1/2]array->scanner_y |-> prophecyY;
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_load_int_ghop(pidY, &array->y, pre_, post_)() {
            assert is_atomic_load_int_op(?op, _, _, ?P, ?Q);
            open pre_();
            popl20_open_atomic_space();
            open atomic_space_inv(array)();
            op();
            array->scan_y_state = 2;
            close post_(prophecyY);
            close atomic_space_inv(array)();
            popl20_close_atomic_space();
        };
        @*/
        //@ close pre_();
        vy = atomic_load_int(pidY, &array->y);
        //@ open post_(_);
    }
    {
        /*@
        predicate pre_() =
            [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
            [_]array->inv |-> inv &*&
            [_]array->Sid |-> Sid &*&
            [_]array->xid |-> xid &*&
            [_]array->fxid |-> fxid &*&
            [_]array->yid |-> yid &*&
            [_]array->fyid |-> fyid &*&
            [1/2]tracked_int(Sid, &array->S, 1, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 2 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scanner_rx |-> _ &*&
            [1/2]array->scan_y_state |-> 2 &*&
            [1/2]array->scanner_y |-> prophecyY &*&
            [1/2]array->scanner_ry |-> _ &*&
            is_array_scan_ghop(ghop, inv, pre, post) &*& pre() &*&
            prophecy(pidS0, Sid, prophecyS0, prophecyS0NbWrites, prophecyS0NbReads);
        predicate post_() =
            [1/2]tracked_int(Sid, &array->S, 0, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 3 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scanner_rx |-> ?rx &*&
            [1/2]array->scan_y_state |-> 3 &*&
            [1/2]array->scanner_y |-> prophecyY &*&
            [1/2]array->scanner_ry |-> ?ry &*&
            post(rx, ry);
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_store_int_ghop(pidS0, &array->S, 0, pre_, post_)() {
            assert is_atomic_store_int_op(?op, _, _, _, ?P, ?Q);
            open pre_();
            popl20_open_atomic_space();
            open atomic_space_inv(array)();
            assert inv(?rx, ?ry);
            op();
            array->scanner_rx = rx;
            array->scan_x_state = 3;
            array->scanner_ry = ry;
            array->scan_y_state = 3;
            ghop();
            leak is_array_scan_ghop(ghop, inv, pre, post);
            if (array->write_x_delayed_state != 0 && prophecyS0NbWrites == array->write_x_scan_cycle) {
                assert is_array_write_x_ghop(?write_x_ghop, inv, _, _, _);
                write_x_ghop();
                leak is_array_write_x_ghop(_, _, _, _, _);
            }
            if (array->write_x_state == 1) {
                tracked_int_match_prophecy(array->write_x_read_S_prophecy_id);
            }
            if (array->write_y_delayed_state != 0 && prophecyS0NbWrites == array->write_y_scan_cycle) {
                assert is_array_write_y_ghop(?write_y_ghop, inv, _, _, _);
                write_y_ghop();
                leak is_array_write_y_ghop(_, _, _, _, _);
            }
            if (array->write_y_state == 1) {
                tracked_int_match_prophecy(array->write_y_read_S_prophecy_id);
            }
            close post_();
            close atomic_space_inv(array)();
            popl20_close_atomic_space();
        };
        @*/
        //@ close pre_();
        atomic_store_int(pidS0, &array->S, 0);
        //@ open post_();
    }
    //@ assert post(?rx, ?ry);
    int ox;
    {
        /*@
        predicate pre_() =
            [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
            [_]array->inv |-> inv &*&
            [_]array->Sid |-> Sid &*&
            [_]array->xid |-> xid &*&
            [_]array->fxid |-> fxid &*&
            [_]array->yid |-> yid &*&
            [_]array->fyid |-> fyid &*&
            [1/2]tracked_int(Sid, &array->S, 0, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 3 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scanner_rx |-> rx &*&
            [1/2]array->scan_y_state |-> 3 &*&
            [1/2]array->scanner_y |-> prophecyY &*&
            [1/2]array->scanner_ry |-> ry &*&
            prophecy(pidFX, fxid, prophecyFX, prophecyFXNbWrites, prophecyFXNbReads);
        predicate post_(int result) =
            result == prophecyFX &*&
            [1/2]tracked_int(Sid, &array->S, 0, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 0 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scanner_rx |-> rx &*&
            [1/2]array->scan_y_state |-> 3 &*&
            [1/2]array->scanner_y |-> prophecyY &*&
            [1/2]array->scanner_ry |-> ry &*&
            prophecyFX == INT_MIN ?
                rx == prophecyX
            :
                rx == prophecyFX;
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_load_int_ghop(pidFX, &array->fx, pre_, post_)() {
            assert is_atomic_load_int_op(?op, _, _, ?P, ?Q);
            open pre_();
            popl20_open_atomic_space();
            open atomic_space_inv(array)();
            op();
            array->scan_x_state = 0;
            assert [_]tracked_int(Sid, &array->S, ?S, ?S_nbWrites);
            if (array->write_x_state == 2 && array->write_x_delayed_state == 0) {
                tracked_int_reads_tracker_match_prophecy(array->write_x_write_fx_prophecy_id);
                assert prophecyFX == INT_MIN || array->write_x_write_fx_nbReads <= prophecyFXNbReads;
            } else {
            }
            close post_(prophecyFX);
            close atomic_space_inv(array)();
            popl20_close_atomic_space();
        };
        @*/
        //@ close pre_();
        ox = atomic_load_int(pidFX, &array->fx);
        //@ open post_(_);
    }
    int oy;
    {
        /*@
        predicate pre_() =
            [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
            [_]array->inv |-> inv &*&
            [_]array->Sid |-> Sid &*&
            [_]array->xid |-> xid &*&
            [_]array->fxid |-> fxid &*&
            [_]array->yid |-> yid &*&
            [_]array->fyid |-> fyid &*&
            [1/2]tracked_int(Sid, &array->S, 0, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 0 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scanner_rx |-> rx &*&
            [1/2]array->scan_y_state |-> 3 &*&
            [1/2]array->scanner_y |-> prophecyY &*&
            [1/2]array->scanner_ry |-> ry &*&
            prophecy(pidFY, fyid, prophecyFY, prophecyFYNbWrites, prophecyFYNbReads);
        predicate post_(int result) =
            result == prophecyFY &*&
            [1/2]tracked_int(Sid, &array->S, 0, ?S_nbWrites) &*&
            [1/2]tracked_int_reads_tracker(xid, ?x_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fxid, ?fx_nbReads) &*&
            [1/2]tracked_int_reads_tracker(yid, ?y_nbReads) &*&
            [1/2]tracked_int_reads_tracker(fyid, ?fy_nbReads) &*&
            [1/2]array->scan_x_state |-> 0 &*&
            [1/2]array->scanner_x |-> prophecyX &*&
            [1/2]array->scanner_rx |-> rx &*&
            [1/2]array->scan_y_state |-> 0 &*&
            [1/2]array->scanner_y |-> prophecyY &*&
            [1/2]array->scanner_ry |-> ry &*&
            prophecyFY == INT_MIN ?
                ry == prophecyY
            :
                ry == prophecyFY;
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_load_int_ghop(pidFY, &array->fy, pre_, post_)() {
            assert is_atomic_load_int_op(?op, _, _, ?P, ?Q);
            open pre_();
            popl20_open_atomic_space();
            open atomic_space_inv(array)();
            op();
            array->scan_y_state = 0;
            assert [_]tracked_int(Sid, &array->S, ?S, ?S_nbWrites);
            if (array->write_y_state == 2 && array->write_y_delayed_state == 0) {
                tracked_int_reads_tracker_match_prophecy(array->write_y_write_fy_prophecy_id);
                assert prophecyFY == INT_MIN || array->write_y_write_fy_nbReads <= prophecyFYNbReads;
            } else {
            }
            close post_(prophecyFY);
            close atomic_space_inv(array)();
            popl20_close_atomic_space();
        };
        @*/
        //@ close pre_();
        oy = atomic_load_int(pidFY, &array->fy);
        //@ open post_(_);
    }
    *px = ox != INT_MIN ? ox : vx;
    *py = oy != INT_MIN ? oy : vy;
}

void array_write_y(array_t array, int value)
    /*@
    requires
        array_y_writer(array, ?inv) &*& value != INT_MIN &*&
        is_array_write_y_ghop(?ghop, inv, value, ?pre, ?post) &*& pre();
    @*/
    //@ ensures array_y_writer(array, inv) &*& post();
{
    //@ open array_y_writer(array, inv);
    //@ int_tracker Sid = array->Sid;
    //@ int_tracker yid = array->yid;
    //@ int_tracker fyid = array->fyid;
    
    prophecy_id pidX = create_prophecy(array->yid);
    //@ assert prophecy(pidX, yid, ?prophecyX, ?prophecyXNbWrites, ?prophecyXNbReads);
    
    prophecy_id pidS = create_prophecy(array->Sid);
    //@ assert prophecy(pidS, Sid, ?prophecyS, ?prophecySNbWrites, ?prophecySNbReads);
    
    prophecy_id pidFX = create_prophecy(array->fyid);
    //@ assert prophecy(pidFX, fyid, ?prophecyFX, ?prophecyFXNbWrites, ?prophecyFXNbReads);

    {
        /*@
        predicate pre_() =
            [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
            [_]array->inv |-> inv &*&
            [_]array->Sid |-> Sid &*&
            [_]array->yid |-> yid &*&
            [_]array->fyid |-> fyid &*&
            [1/2]tracked_int(yid, &array->y, _, _) &*&
            [1/2]array->write_y_state |-> 0 &*&
            [1/2]array->write_y_scan_cycle |-> _ &*&
            [1/2]array->write_y_delayed_state |-> 0 &*&
            [1/2]array->write_y_read_S_nbWrites |-> _ &*&
            [1/2]array->write_y_read_S_prophecy_id |-> _ &*&
            [1/2]array->write_y_write_fy_nbReads |-> _ &*&
            [1/2]array->write_y_write_fy_prophecy_id |-> _ &*&
            [1/2]array->write_y_post |-> _ &*&
            [1/2]prophecy(pidS, Sid, prophecyS, prophecySNbWrites, prophecySNbReads) &*&
            is_array_write_y_ghop(ghop, inv, value, pre, post) &*& pre() &*&
            prophecy(pidX, yid, prophecyX, prophecyXNbWrites, prophecyXNbReads);
        predicate post_() =
            [1/2]tracked_int(yid, &array->y, value, _) &*&
            [1/2]array->write_y_state |-> 1 &*&
            [1/2]array->write_y_scan_cycle |-> _ &*&
            [1/2]array->write_y_delayed_state |-> ?delayedState &*&
            [1/2]array->write_y_read_S_nbWrites |-> prophecySNbWrites &*&
            [1/2]array->write_y_read_S_prophecy_id |-> pidS &*&
            [1/2]array->write_y_write_fy_nbReads |-> prophecyFXNbReads &*&
            [1/2]array->write_y_write_fy_prophecy_id |-> pidFX &*&
            [1/2]array->write_y_post |-> post &*&
            (delayedState != 0 ? true : post());
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_store_int_ghop(pidX, &array->y, value, pre_, post_)() {
            assert is_atomic_store_int_op(?op, _, _, _, ?P, ?Q);
            open pre_();
            popl20_open_atomic_space();
            open atomic_space_inv(array)();
            assert [_]tracked_int(Sid, &array->S, ?S, ?S_nbWrites);
            assert tracked_int(yid, &array->y, ?y, ?y_nbWrites);
            assert [_]tracked_int(fyid, &array->fy, ?fy, ?fy_nbWrites) &*& [_]tracked_int_reads_tracker(fyid, ?fy_nbReads);
            array->write_y_state = 1;
            array->write_y_scan_cycle = S_nbWrites;
            array->write_y_read_S_nbWrites = prophecySNbWrites;
            array->write_y_read_S_prophecy_id = pidS;
            array->write_y_write_fy_nbReads = prophecyFXNbReads;
            array->write_y_write_fy_prophecy_id = pidFX;
            array->write_y_post = post;
            if ((array->scan_y_state == 1 && fy != INT_MIN || array->scan_y_state == 2) && (prophecySNbWrites > S_nbWrites || prophecyFXNbReads > fy_nbReads)) {
                if (prophecySNbWrites > S_nbWrites)
                    array->write_y_delayed_state = 1;
                else
                    array->write_y_delayed_state = 2;
            } else {
                ghop();
                leak is_array_write_y_ghop(_, _, _, _, _);
            }
            produce_func_lt(atomic_store_int);
            op();
            close post_();
            close atomic_space_inv(array)();
            popl20_close_atomic_space();
        };
        @*/
        //@ close pre_();
        atomic_store_int(pidX, &array->y, value);
        //@ open post_();
    }
    //@ int write_y_scan_cycle = array->write_y_scan_cycle;
    //@ int delayedState = array->write_y_delayed_state;
    int write_y_S;
    {
        /*@
        predicate pre_() =
            [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
            [_]array->inv |-> inv &*&
            [_]array->Sid |-> Sid &*&
            [_]array->yid |-> yid &*&
            [_]array->fyid |-> fyid &*&
            [1/2]tracked_int(yid, &array->y, value, _) &*&
            [1/2]array->write_y_state |-> 1 &*&
            [1/2]array->write_y_scan_cycle |-> write_y_scan_cycle &*&
            [1/2]array->write_y_delayed_state |-> delayedState &*&
            [1/2]array->write_y_read_S_nbWrites |-> prophecySNbWrites &*&
            [1/2]array->write_y_read_S_prophecy_id |-> pidS &*&
            [1/2]array->write_y_write_fy_nbReads |-> prophecyFXNbReads &*&
            [1/2]array->write_y_write_fy_prophecy_id |-> pidFX &*&
            (prophecyS != 0 ? [1/2]prophecy(pidFX, fyid, prophecyFX, prophecyFXNbWrites, prophecyFXNbReads) : true) &*&
            [1/2]array->write_y_post |-> post &*&
            [1/2]prophecy(pidS, Sid, prophecyS, prophecySNbWrites, prophecySNbReads);
        predicate post_(int result) =
            result == prophecyS &*&
            [1/2]tracked_int(yid, &array->y, value, _) &*&
            [1/2]array->write_y_read_S_nbWrites |-> prophecySNbWrites &*&
            [1/2]array->write_y_read_S_prophecy_id |-> pidS &*&
            [1/2]array->write_y_write_fy_nbReads |-> prophecyFXNbReads &*&
            [1/2]array->write_y_write_fy_prophecy_id |-> pidFX &*&
            [1/2]array->write_y_scan_cycle |-> write_y_scan_cycle &*&
            [1/2]array->write_y_post |-> post &*&
            [1/2]array->write_y_state |-> (prophecyS == 0 ? 0 : 2) &*&
            delayedState == 1 ?
                [1/2]array->write_y_delayed_state |-> 0 &*& post()
            :
                [1/2]array->write_y_delayed_state |-> delayedState &*& delayedState == 0 || prophecyS != 0;
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_load_int_ghop(pidS, &array->S, pre_, post_)() {
            assert is_atomic_load_int_op(?op, _, _, ?P, ?Q);
            open pre_();
            popl20_open_atomic_space();
            open atomic_space_inv(array)();
            assert [_]tracked_int(Sid, &array->S, ?S, ?S_nbWrites);
            array->write_y_state = prophecyS == 0 ? 0 : 2;
            op();
            if (delayedState == 1)
                array->write_y_delayed_state = 0;
            close post_(prophecyS);
            close atomic_space_inv(array)();
            popl20_close_atomic_space();
        };
        @*/
        //@ close pre_();
        write_y_S = atomic_load_int(pidS, &array->S);
        //@ open post_(_);
    }
    //@ int newDelayedState = array->write_y_delayed_state;
    //@ assert newDelayedState != 1;
    if (write_y_S) {
        /*@
        predicate pre_() =
            [_]popl20_atomic_space(create_array, atomic_space_inv(array)) &*&
            [_]array->inv |-> inv &*&
            [_]array->Sid |-> Sid &*&
            [_]array->yid |-> yid &*&
            [_]array->fyid |-> fyid &*&
            [1/2]tracked_int(yid, &array->y, value, _) &*&
            [1/2]array->write_y_state |-> 2 &*&
            [1/2]array->write_y_scan_cycle |-> write_y_scan_cycle &*&
            [1/2]array->write_y_delayed_state |-> newDelayedState &*&
            [1/2]array->write_y_read_S_nbWrites |-> prophecySNbWrites &*&
            [1/2]array->write_y_write_fy_nbReads |-> prophecyFXNbReads &*&
            [1/2]array->write_y_write_fy_prophecy_id |-> pidFX &*&
            [1/2]array->write_y_post |-> post &*&
            [1/2]prophecy(pidFX, fyid, prophecyFX, prophecyFXNbWrites, prophecyFXNbReads);
        predicate post_() =
            [1/2]tracked_int(yid, &array->y, value, _) &*&
            [1/2]array->write_y_read_S_nbWrites |-> prophecySNbWrites &*&
            [1/2]array->write_y_write_fy_nbReads |-> prophecyFXNbReads &*&
            [1/2]array->write_y_write_fy_prophecy_id |-> pidFX &*&
            [1/2]array->write_y_scan_cycle |-> write_y_scan_cycle &*&
            [1/2]array->write_y_post |-> post &*&
            [1/2]array->write_y_state |-> 0 &*&
            [1/2]array->write_y_delayed_state |-> 0 &*&
            (newDelayedState != 0 ? post() : true);
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_store_int_ghop(pidFX, &array->fy, value, pre_, post_)() {
            assert is_atomic_store_int_op(?op, _, _, _, ?P, ?Q);
            open pre_();
            popl20_open_atomic_space();
            open atomic_space_inv(array)();
            array->write_y_state = 0;
            op();
            array->write_y_delayed_state = 0;
            assert [_]tracked_int(Sid, &array->S, ?S, ?S_nbWrites);
            if (array->scan_y_state == 3) {
                if (array->write_y_delayed_state != 0) {
                } else if (array->write_y_scan_cycle != S_nbWrites - 1) {
                    assert array->write_y_scan_cycle < S_nbWrites - 1;
                    assert array->scanner_ry == value;
                }
            }
            close post_();
            close atomic_space_inv(array)();
            popl20_close_atomic_space();
        };
        @*/
        //@ close pre_();
        atomic_store_int(pidFX, &array->fy, value);
        //@ open post_();
    }
    //@ if (!write_y_S) { leak prophecy(pidFX, _, _, _, _); } 
}
