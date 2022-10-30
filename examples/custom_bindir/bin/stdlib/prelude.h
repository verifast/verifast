#ifndef PRELUDE_H
#define PRELUDE_H

/*@

inductive list<t> = nil | cons(t, list<t>);

fixpoint int length<t>(list<t> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return 1 + length(xs0);
    }
}

abstract_type pointer_provenance;
inductive pointer = pointer_ctor(pointer_provenance provenance, uintptr_t address);

fixpoint pointer ptr_add(pointer p, int offset) {
    return pointer_ctor(p.provenance, p.address + offset);
}

fixpoint pointer_provenance field_ptr_provenance(pointer p, int fieldOffset);
fixpoint pointer field_ptr_provenance_parent(pointer_provenance pr, int fieldOffset);

lemma_auto(field_ptr_provenance(p, fieldOffset)) void field_ptr_provenance_injective(pointer p, int fieldOffset);
    requires true;
    ensures field_ptr_provenance_parent(field_ptr_provenance(p, fieldOffset), fieldOffset) == p;

fixpoint pointer field_ptr(pointer p, int fieldOffset) {
    return pointer_ctor(field_ptr_provenance(p, fieldOffset), p.address + fieldOffset);
}
fixpoint pointer_provenance union_variant_ptr_provenance(pointer p, int variantId) {
    return p.provenance; // TODO: enforce strict aliasing (a.k.a. "effective types")
}
fixpoint pointer union_variant_ptr(pointer p, int variantId) {
    return pointer_ctor(union_variant_ptr_provenance(p, variantId), p.address);
}

fixpoint pointer_provenance null_pointer_provenance();
fixpoint pointer null_pointer() { return pointer_ctor(null_pointer_provenance, 0); }

fixpoint uintptr_t ptr_provenance_min_addr(pointer_provenance pr);
fixpoint uintptr_t ptr_provenance_max_addr(pointer_provenance pr);

fixpoint bool ptr_within_limits(pointer p) {
    return ptr_provenance_min_addr(p.provenance) <= p.address && p.address <= ptr_provenance_max_addr(p.provenance);
}

fixpoint bool pointer_within_limits(void *p) {
    return ptr_within_limits((pointer)p);
}

fixpoint bool object_pointer_within_limits(void *p, int size) {
    return pointer_within_limits(p) && pointer_within_limits(p + size) && 0 < (uintptr_t)p;
}

predicate custom_chars(char *array, int size, list<char> cs);

lemma_auto void custom_chars_inv();
    requires [?f]custom_chars(?array, ?count, ?cs);
    ensures [f]custom_chars(array, count, cs) &*& length(cs) == count;

predicate malloc_block(void *p; int size);

@*/

typedef int main();
    //@ requires true;
    //@ ensures true;

#endif
