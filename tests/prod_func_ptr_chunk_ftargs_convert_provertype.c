typedef void vector_init_elem/*@ <t> (predicate (void*;t) entp, t val) @*/(void* elem);
//@ requires chars(elem, 4, _);
//@ ensures entp(elem, val);

static void null_init(void *obj);
//@ requires chars(obj, 4, _);
//@ ensures integer(obj, 0);

void to_verify()
//@ requires true;
//@ ensures true;
{
    /*@
    produce_function_pointer_chunk vector_init_elem<int>(null_init)(integer, 0)(a) {call();}
    @*/
}