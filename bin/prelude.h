#ifndef PRELUDE_H
#define PRELUDE_H

//@ #include "prelude_core.gh"
//@ #include "list.gh"

/*@

lemma void assume(bool b);
    requires true;
    ensures b;

predicate exists<t>(t x;) = true;

fixpoint int truncate_unsigned(int x, int nbBits);
fixpoint int truncate_signed(int x, int nbBits); // nbBits does not include the sign bit

fixpoint int abs(int x) { return x < 0 ? -x : x; }

lemma void mul_mono_l(int x, int y, int z);
    requires x <= y &*& 0 <= z;
    ensures x * z <= y * z;

lemma void div_rem(int D, int d);
    requires d != 0;
    ensures D == D / d * d + D % d &*& abs(D % d) < abs(d) &*& abs(D / d * d) <= abs(D);

lemma void div_rem_nonneg(int D, int d);
    requires 0 <= D &*& 0 < d;
    ensures D == D / d * d + D % d &*& 0 <= D / d &*& D / d <= D &*& 0 <= D % d &*& D % d < d;

lemma void div_rem_nonneg_unique(int D, int d, int q, int r);
    requires 0 <= D &*& 0 <= r &*& r < d &*& D == d * q + r;
    ensures D / d == q &*& D % d == r;

inductive pointer_provenance =
    pointer_provenance_ctor(int); // Do not rely on this definition; it is subject to change.
inductive pointer = pointer_ctor(pointer_provenance provenance, uintptr_t address);

fixpoint pointer ptr_add(pointer p, int offset) {
    return pointer_ctor(p.provenance, p.address + offset);
}

fixpoint pointer_provenance field_ptr_provenance(pointer p, void *structTypeid, int fieldOffset);
fixpoint pointer_provenance field_ptr_provenance_parent(pointer_provenance pr);

lemma_auto(field_ptr_provenance(p, structTypeid, fieldOffset)) void field_ptr_provenance_injective(pointer p, void *structTypeid, int fieldOffset);
    requires true;
    ensures field_ptr_provenance_parent(field_ptr_provenance(p, structTypeid, fieldOffset)) == p.provenance;

fixpoint pointer field_ptr(pointer p, void *structTypeid, int fieldOffset) {
    return pointer_ctor(field_ptr_provenance(p, structTypeid, fieldOffset), p.address + fieldOffset);
}

fixpoint pointer field_ptr_parent(pointer p, int fieldOffset) {
    return pointer_ctor(
        field_ptr_provenance_parent(p.provenance), 
        p.address - fieldOffset
    );
}

fixpoint pointer_provenance union_variant_ptr_provenance(pointer p, void *unionTypeId, int variantId);
fixpoint pointer union_variant_ptr(pointer p, void *unionTypeid, int variantId) {
    return pointer_ctor(union_variant_ptr_provenance(p, unionTypeid, variantId), p.address);
}

fixpoint pointer_provenance null_pointer_provenance();
fixpoint pointer null_pointer() { return pointer_ctor(null_pointer_provenance, 0); }

fixpoint uintptr_t ptr_provenance_min_addr(pointer_provenance pr);
fixpoint uintptr_t ptr_provenance_max_addr(pointer_provenance pr);

lemma_auto void ptr_provenance_min_addr_limits(pointer_provenance pr);
    requires true;
    ensures 0 <= ptr_provenance_min_addr(pr);

lemma_auto void ptr_provenance_max_addr_limits(pointer_provenance pr);
    requires true;
    ensures ptr_provenance_max_addr(pr) <= UINTPTR_MAX;

lemma_auto void null_pointer_provenance_min_addr();
    requires true;
    ensures ptr_provenance_min_addr(null_pointer_provenance) == 0;

lemma_auto void null_pointer_provenance_max_addr();
    requires true;
    ensures ptr_provenance_max_addr(null_pointer_provenance) == UINTPTR_MAX;

lemma_auto void field_ptr_provenance_min_addr(pointer p, void *structTypeid, int fieldOffset);
    requires true;
    ensures ptr_provenance_min_addr(p.provenance) <= ptr_provenance_min_addr(field_ptr_provenance(p, structTypeid, fieldOffset));

lemma_auto void field_ptr_provenance_max_addr(pointer p, void *structTypeid, int fieldOffset);
    requires true;
    ensures ptr_provenance_max_addr(field_ptr_provenance(p, structTypeid, fieldOffset)) <= ptr_provenance_max_addr(p.provenance);

lemma void ptr_provenance_min_addr_zero(pointer_provenance pr);
    requires ptr_provenance_min_addr(pr) <= 0;
    ensures pr == null_pointer_provenance;

fixpoint bool ptr_within_limits(pointer p) {
    return ptr_provenance_min_addr(p.provenance) <= p.address && p.address <= ptr_provenance_max_addr(p.provenance);
}

fixpoint bool pointer_within_limits(void *p) {
    return ptr_within_limits((pointer)p);
}

fixpoint bool object_pointer_within_limits(void *p, int size) {
    return pointer_within_limits(p) && pointer_within_limits(p + size) && (uintptr_t)p != 0 && size >= 0;
}

// When producing a field chunk, VeriFast produces a field_pointer_within_limits fact
// instead of a pointer_within_limits fact to avoid producing too many linear inequalities.
fixpoint bool field_pointer_within_limits(void *p, int fieldOffset);

lemma_auto(pointer_within_limits((void *)field_ptr((pointer)p, structTypeid, fieldOffset))) void field_pointer_within_limits_def(void *p, void *structTypeid, int fieldOffset);
    requires true;
    ensures field_pointer_within_limits(p, fieldOffset) == pointer_within_limits((void *)field_ptr((pointer)p, structTypeid, fieldOffset));

lemma_auto(field_pointer_within_limits((void *)field_ptr((pointer)p, structTypeid, fieldOffset), 0)) void first_field_pointer_within_limits_elim(void *p, void *structTypeid, int fieldOffset);
    requires true;
    ensures field_pointer_within_limits((void *)field_ptr((pointer)p, structTypeid, fieldOffset), 0) == field_pointer_within_limits(p, fieldOffset);

lemma_auto(field_pointer_within_limits((void *)union_variant_ptr(field_ptr((pointer)p, structTypeid, fieldOffset), unionTypeid, variantId), 0)) void first_field_of_union_variant_pointer_within_limits_elim(void *p, void *structTypeid, int fieldOffset, void *unionTypeid, int variantId);
    requires true;
    ensures field_pointer_within_limits((void *)union_variant_ptr(field_ptr((pointer)p, structTypeid, fieldOffset), unionTypeid, variantId), 0) == field_pointer_within_limits(p, fieldOffset);

lemma_auto(ptr_within_limits(field_ptr(p, structTypeid, 0))) void ptr_within_limits_field_ptr_0(pointer p, void *structTypeid);
    requires true;
    ensures ptr_within_limits(field_ptr(p, structTypeid, 0)) == ptr_within_limits(p);

fixpoint bool has_type(void *p, void *typeid_);

lemma_auto void has_type_short_ushort(void *p);
    requires true;
    ensures has_type(p, &typeid(short)) == has_type(p, &typeid(unsigned short));

lemma_auto void has_type_int_uint(void *p);
    requires true;
    ensures has_type(p, &typeid(int)) == has_type(p, &typeid(unsigned int));

lemma_auto void has_type_long_ulong(void *p);
    requires true;
    ensures has_type(p, &typeid(long)) == has_type(p, &typeid(unsigned long));

lemma_auto void has_type_llong_ullong(void *p);
    requires true;
    ensures has_type(p, &typeid(long long)) == has_type(p, &typeid(unsigned long long));

lemma_auto void has_type_intptr_uintptr(void *p);
    requires true;
    ensures has_type(p, &typeid(intptr_t)) == has_type(p, &typeid(uintptr_t));

lemma_auto void has_type_int8_uint8(void *p);
    requires true;
    ensures has_type(p, &typeid(__int8)) == has_type(p, &typeid(unsigned __int8));

lemma_auto void has_type_int16_uint16(void *p);
    requires true;
    ensures has_type(p, &typeid(__int16)) == has_type(p, &typeid(unsigned __int16));

lemma_auto void has_type_int32_uint32(void *p);
    requires true;
    ensures has_type(p, &typeid(__int32)) == has_type(p, &typeid(unsigned __int32));

lemma_auto void has_type_int64_uint64(void *p);
    requires true;
    ensures has_type(p, &typeid(__int64)) == has_type(p, &typeid(unsigned __int64));

lemma_auto void has_type_int128_uint128(void *p);
    requires true;
    ensures has_type(p, &typeid(__int128)) == has_type(p, &typeid(unsigned __int128));

fixpoint pointer ptr_add_(pointer p, int offset, void *elemTypeid) {
    return ptr_add(p, offset * sizeof((pointer)elemTypeid));
}

lemma_auto(has_type((void *)ptr_add_(p, offset, elemTypeid), elemTypeid)) void has_type_ptr_add_(pointer p, int offset, void *elemTypeid);
    requires true;
    ensures has_type((void *)ptr_add_(p, offset, elemTypeid), elemTypeid) == has_type((void *)p, elemTypeid);

predicate generic_points_to_<t>(t *p; option<t> v);
predicate generic_points_to<t>(t *p; t v) = generic_points_to_(p, some(v));

predicate integer__(void *p, int size, bool signed_; option<int> v);
predicate integer_(void *p, int size, bool signed_; int v) = integer__(p, size, signed_, some(v));

predicate char_(char *p; option<char> v) = integer__(p, 1, true, v);
predicate uchar_(unsigned char *p; option<unsigned char> v) = integer__(p, 1, false, v);

predicate character(char *p; char c) = char_(p, some(c));
predicate u_character(unsigned char *p; unsigned char c) = uchar_(p, some(c));

predicate int_(int *p; option<int> v) = integer__(p, sizeof(int), true, v) &*& has_type(p, &typeid(int)) == true;
predicate uint_(unsigned int *p; option<int> v) = integer__(p, sizeof(int), false, v) &*& has_type(p, &typeid(unsigned int)) == true;

predicate integer(int *p; int v) = int_(p, some(v));
predicate u_integer(unsigned int *p; unsigned int v) = uint_(p, some(v));

predicate long_(long *p; option<long> v) = integer__(p, sizeof(long), true, v) &*& has_type(p, &typeid(long)) == true;
predicate ulong_(unsigned long *p; option<unsigned long> v) = integer__(p, sizeof(long), false, v) &*& has_type(p, &typeid(unsigned long)) == true;

predicate long_integer(long *p; long v) = long_(p, some(v));
predicate ulong_integer(unsigned long *p; unsigned long v) = ulong_(p, some(v));

predicate llong_(long long *p; option<long long> v) = integer__(p, sizeof(long long), true, v) &*& has_type(p, &typeid(long long)) == true;
predicate ullong_(unsigned long long *p; option<unsigned long long> v) = integer__(p, sizeof(long long), false, v) &*& has_type(p, &typeid(unsigned long long)) == true;

predicate llong_integer(long long *p; long long l) = integer_(p, sizeof(long long), true, l);
predicate u_llong_integer(unsigned long long *p; unsigned long long l) = integer_(p, sizeof(long long), false, l);

lemma_auto void llong_integer_to_llong_(long long *p);
    requires [?f]llong_integer(p, ?v);
    ensures [f]llong_(p, some(v));

lemma_auto void u_llong_integer_to_ullong_(unsigned long long *p);
    requires [?f]u_llong_integer(p, ?v);
    ensures [f]ullong_(p, some(v));

predicate short_(short *p; option<short> v) = integer__(p, sizeof(short), true, v) &*& has_type(p, &typeid(short)) == true;
predicate ushort_(unsigned short *p; option<unsigned short> v) = integer__(p, sizeof(short), false, v) &*& has_type(p, &typeid(unsigned short)) == true;

predicate short_integer(short *p; short s) = short_(p, some(s));
predicate u_short_integer(unsigned short *p; unsigned short v) = ushort_(p, some(v));

predicate intptr_(intptr_t *p; option<intptr_t> v) = integer__(p, sizeof(intptr_t), true, v) &*& has_type(p, &typeid(intptr_t)) == true;
predicate uintptr_(uintptr_t *p; option<uintptr_t> v) = integer__(p, sizeof(uintptr_t), false, v) &*& has_type(p, &typeid(uintptr_t)) == true;

predicate intptr(intptr_t *p; intptr_t v) = intptr_(p, some(v));
predicate uintptr(uintptr_t *p; uintptr_t v) = uintptr_(p, some(v));

predicate pointer_(void **pp; option<void *> p);
predicate pointer(void **pp; void *p) = pointer_(pp, some(p));

predicate bool_(bool *p; option<bool> v);
predicate boolean(bool* p; bool v) = bool_(p, some(v));

predicate float__(float *p; option<float> v);
predicate double__(double *p; option<double> v);
predicate long_double_(long double *p; option<long double> v);

predicate float_(float *p; float v) = float__(p, some(v));
predicate double_(double *p; double v) = double__(p, some(v));
predicate long_double(long double *p; long double v) = long_double_(p, some(v));

lemma void integer__distinct(void *i, void *j);
    requires integer_(i, ?size1, ?signed1, ?v1) &*& integer_(j, ?size2, ?signed2, ?v2);
    ensures integer_(i, size1, signed1, v1) &*& integer_(j, size2, signed2, v2) &*& (uintptr_t)i != (uintptr_t)j;

lemma void integer___unique(void *p);
    requires [?f]integer__(p, ?size, ?signed_, ?v);
    ensures [f]integer__(p, size, signed_, v) &*& f <= 1;

lemma void integer__unique(void *p);
    requires [?f]integer_(p, ?size, ?signed_, ?v);
    ensures [f]integer_(p, size, signed_, v) &*& f <= 1;

lemma void integer__limits(void *p);
    requires [?f]integer_(p, ?size, ?signed_, ?v);
    ensures [f]integer_(p, size, signed_, v) &*& object_pointer_within_limits(p, size) == true &*& size > 0 &*& signed_ ? -(1<<(8*size-1)) <= v &*& v < (1<<(8*size-1)) : 0 <= v &*& v < (1<<(8*size));

lemma void integer___limits(void *p);
    requires [?f]integer__(p, ?size, ?signed_, ?v);
    ensures [f]integer__(p, size, signed_, v) &*& object_pointer_within_limits(p, size) == true &*& size > 0;

lemma void char__limits(char *pc);
    requires [?f]char_(pc, ?c);
    ensures [f]char_(pc, c) &*& object_pointer_within_limits(pc, 1) == true;

lemma void character_limits(char *pc);
    requires [?f]character(pc, ?c);
    ensures [f]character(pc, c) &*& object_pointer_within_limits(pc, 1) == true &*& CHAR_MIN <= c &*& c <= CHAR_MAX;

lemma void u_character_limits(unsigned char *pc);
    requires [?f]u_character(pc, ?c);
    ensures [f]u_character(pc, c) &*& object_pointer_within_limits(pc, 1) == true &*& 0 <= c &*& c <= UCHAR_MAX;

lemma void integer_distinct(int* i, int* j);
    requires integer(i, ?v1) &*& integer(j, ?v2);
    ensures integer(i, v1) &*& integer(j, v2) &*& (uintptr_t)i != (uintptr_t)j;

lemma void integer_unique(int *p);
    requires [?f]integer(p, ?v);
    ensures [f]integer(p, v) &*& f <= 1;

lemma void integer_limits(int *p);
    requires [?f]integer(p, ?v);
    ensures [f]integer(p, v) &*& object_pointer_within_limits(p, sizeof(int)) == true &*& INT_MIN <= v &*& v <= INT_MAX;

lemma void u_integer_limits(unsigned int *p);
    requires [?f]u_integer(p, ?v);
    ensures [f]u_integer(p, v) &*& object_pointer_within_limits(p, sizeof(unsigned int)) == true &*& 0 <= v &*& v <= UINT_MAX;

lemma void short_integer_limits(short *p);
    requires [?f]short_integer(p, ?v);
    ensures [f]short_integer(p, v) &*& object_pointer_within_limits(p, sizeof(short)) == true &*& SHRT_MIN <= v &*& v <= SHRT_MAX;

lemma void u_short_integer_limits(unsigned short *p);
    requires [?f]u_short_integer(p, ?v);
    ensures [f]u_short_integer(p, v) &*& object_pointer_within_limits(p, sizeof(unsigned short)) == true &*& 0 <= v &*& v <= USHRT_MAX;

lemma void pointer_distinct(void *pp1, void *pp2);
    requires pointer(pp1, ?p1) &*& pointer(pp2, ?p2);
    ensures pointer(pp1, p1) &*& pointer(pp2, p2) &*& (uintptr_t)pp1 != (uintptr_t)pp2;

lemma void pointer_fractions_same_address(void *pp1, void *pp2);
    requires [?f1]pointer(pp1, ?p1) &*& [?f2]pointer(pp2, ?p2) &*& (uintptr_t)pp1 == (uintptr_t)pp2;
    ensures [f1]pointer(pp1, p1) &*& [f2]pointer(pp2, p2) &*& pp1 == pp2 &*& p2 == p1;

lemma void pointer__fractions_same_address(void *pp1, void *pp2);
    requires [?f1]pointer_(pp1, ?p1) &*& [?f2]pointer_(pp2, ?p2) &*& (uintptr_t)pp1 == (uintptr_t)pp2;
    ensures [f1]pointer_(pp1, p1) &*& [f2]pointer_(pp2, p2) &*& pp1 == pp2 &*& p2 == p1;

lemma void pointer_unique(void *pp);
    requires [?f]pointer(pp, ?p);
    ensures [f]pointer(pp, p) &*& f <= 1;

lemma_auto void pointer_nonzero();
    requires pointer(?pp, ?p);
    ensures pointer(pp, p) &*& (uintptr_t)pp != 0;

lemma void pointer_limits(void *pp);
    requires [?f]pointer(pp, ?p);
    ensures [f]pointer(pp, p) &*& object_pointer_within_limits(pp, sizeof(void *)) == true &*& pointer_within_limits(p) == true;

lemma void boolean_distinct(bool* i, bool* j);
    requires boolean(i, ?v1) &*& boolean(j, ?v2);
    ensures boolean(i, v1) &*& boolean(j, v2) &*& (uintptr_t)i != (uintptr_t)j;

lemma void boolean_unique(bool *p);
    requires [?f]boolean(p, ?v);
    ensures [f]boolean(p, v) &*& f <= 1;

fixpoint void *pointer_of_chars(list<char> cs);
fixpoint list<char> chars_of_pointer(void * p);
fixpoint bool chars_within_limits(list<char> cs);

lemma_auto(pointer_of_chars(chars_of_pointer(p))) void pointer_of_chars_of_pointer(void *p);
    requires p >= (void *)0 && p <= (void *)UINTPTR_MAX;
    ensures pointer_of_chars(chars_of_pointer(p)) == p && chars_within_limits(chars_of_pointer(p)) == true && length(chars_of_pointer(p)) == sizeof(void *);

lemma_auto(chars_of_pointer(pointer_of_chars(cs))) void chars_of_pointer_of_chars(list<char> cs);
    requires length(cs) == sizeof(void *) && chars_within_limits(cs) == true;
    ensures chars_of_pointer(pointer_of_chars(cs)) == cs;

predicate chars_(char *array, int count; list<option<char> > cs) =
    count == 0 ?
        cs == nil
    :
        char_(array, ?c) &*& chars_(array + 1, count - 1, ?cs0) &*& cs == cons(c, cs0);

predicate chars(char *array, int count; list<char> cs) =
    count == 0 ?
        cs == nil
    :
        character(array, ?c) &*& chars(array + 1, count - 1, ?cs0) &*& cs == cons(c, cs0);

lemma_auto void chars_to_chars_(char *array);
    requires [?f]chars(array, ?count, ?cs);
    ensures [f]chars_(array, count, map(some, cs));

lemma_auto void chars__to_chars(char *array);
    requires [?f]chars_(array, ?count, ?cs) &*& cs == map(some, map(the, cs));
    ensures [f]chars(array, count, map(the, cs));

lemma void chars__limits(char *array);
    requires [?f]chars_(array, ?n, ?cs) &*& pointer_within_limits(array) == true;
    ensures [f]chars_(array, n, cs) &*& pointer_within_limits(array + n) == true;

lemma_auto void chars__split(char *array, int offset);
   requires [?f]chars_(array, ?n, ?cs) &*& 0 <= offset &*& offset <= n;
   ensures
       [f]chars_(array, offset, take(offset, cs))
       &*& [f]chars_(array + offset, n - offset, drop(offset, cs))
       &*& append(take(offset, cs), drop(offset, cs)) == cs;

lemma_auto void chars__join(char *array);
    requires [?f]chars_(array, ?n, ?cs) &*& [f]chars_(array + n, ?n0, ?cs0);
    ensures [f]chars_(array, n + n0, append(cs, cs0));

lemma_auto void chars_chars__join(char *array);
    requires [?f]chars(array, ?n, ?cs) &*& [f]chars_(array + n, ?n0, ?cs0);
    ensures [f]chars_(array, n + n0, append(map(some, cs), cs0));

lemma_auto void chars__inv();
    requires [?f]chars_(?array, ?count, ?cs);
    ensures [f]chars_(array, count, cs) &*& length(cs) == count;

lemma_auto void chars_inv();
    requires [?f]chars(?array, ?count, ?cs);
    ensures [f]chars(array, count, cs) &*& length(cs) == count;

lemma void chars_zero();
    requires [?f]chars(0, _, ?cs);
    ensures cs == nil;

lemma void chars_limits(char *array);
    requires [?f]chars(array, ?n, ?cs) &*& pointer_within_limits(array) == true;
    ensures [f]chars(array, n, cs) &*& pointer_within_limits(array + n) == true;

lemma_auto void chars_split(char *array, int offset);
   requires [?f]chars(array, ?n, ?cs) &*& 0 <= offset &*& offset <= n;
   ensures
       [f]chars(array, offset, take(offset, cs))
       &*& [f]chars(array + offset, n - offset, drop(offset, cs))
       &*& append(take(offset, cs), drop(offset, cs)) == cs;

lemma_auto void chars_join(char *array);
    requires [?f]chars(array, ?n, ?cs) &*& [f]chars(array + n, ?n0, ?cs0);
    ensures [f]chars(array, n + n0, append(cs, cs0));

fixpoint int int_of_chars(list<char> cs);
fixpoint list<char> chars_of_int(int i);

lemma_auto(int_of_chars(chars_of_int(i))) void int_of_chars_of_int(int i);
    requires INT_MIN <= i && i <= INT_MAX;
    ensures i == (int_of_chars(chars_of_int(i)));

lemma_auto(chars_of_int(int_of_chars(cs))) void chars_of_int_of_chars(list<char> cs);
    requires true;
    ensures cs == (chars_of_int(int_of_chars(cs)));

lemma void int_of_chars_injective(list<char> cs1, list<char> cs2);
    requires true;
    ensures (cs1 == cs2) == (int_of_chars(cs1) == int_of_chars(cs2));

lemma void chars_of_int_injective(int i1, int i2);
    requires true;
    ensures (i1 == i2) == (chars_of_int(i1) == chars_of_int(i2));

lemma_auto void chars_of_int_size(int i);
    requires INT_MIN <= i && i <= INT_MAX;
    ensures length(chars_of_int(i)) == sizeof(int);

lemma_auto(int_of_chars(cs)) void int_of_chars_size(list<char> cs);
    requires length(cs) == sizeof(int) && chars_within_limits(cs);
    ensures INT_MIN <= int_of_chars(cs) && int_of_chars(cs) <= INT_MAX;

lemma void chars_of_int_char_in_bounds(char c, int i);
    requires INT_MIN <= i && i <= INT_MAX &*&
             true == mem(c, chars_of_int(i));
    ensures  INT_MIN <= c && c <= INT_MAX;

// chars to ...
lemma_auto void chars__to_int_(void *p);
    requires [?f]chars_(p, sizeof(int), _) &*& has_type(p, &typeid(int)) == true;
    ensures [f]int_(p, _);

lemma_auto void chars_to_integer(void *p);
    requires [?f]chars(p, sizeof(int), ?cs) &*& has_type(p, &typeid(int)) == true;
    ensures [f]integer(p, int_of_chars(cs));

lemma_auto void chars_to_u_integer(void *p);
    requires [?f]chars(p, sizeof(unsigned int), ?cs) &*& has_type(p, &typeid(unsigned int)) == true;
    ensures [f]u_integer(p, _);

lemma_auto void chars_to_short_integer(void *p);
    requires [?f]chars(p, sizeof(short), ?cs) &*& has_type(p, &typeid(short)) == true;
    ensures [f]short_integer(p, _);

lemma_auto void chars_to_u_short_integer(void *p);
    requires [?f]chars(p, sizeof(unsigned short), ?cs) &*& has_type(p, &typeid(unsigned short)) == true;
    ensures [f]u_short_integer(p, _);

lemma_auto void chars_to_pointer(void *p);
    requires [?f]chars(p, sizeof(void *), ?cs) &*& has_type(p, &typeid(void *)) == true;
    ensures [f]pointer(p, pointer_of_chars(cs));

lemma_auto void chars_to_boolean(void *p);
    requires [?f]chars(p, sizeof(bool), ?cs) &*& has_type(p, &typeid(bool)) == true;
    ensures [f]boolean(p, _);

lemma_auto void chars_to_integer_(void *p, int size, bool signed_);
    requires [?f]chars(p, size, ?cs);
    ensures [f]integer_(p, size, signed_, _);

// ... to chars
lemma_auto void int__to_chars_(int *p);
    requires [?f]int_(p, _);
    ensures [f]chars_((void *)p, sizeof(int), _) &*& has_type(p, &typeid(int)) == true;

lemma_auto void integer_to_chars(void *p);
    requires [?f]integer(p, ?i);
    ensures [f]chars(p, sizeof(int), chars_of_int(i)) &*& has_type(p, &typeid(int)) == true;

lemma_auto void uint__to_chars_(unsigned int *p);
    requires [?f]uint_(p, _);
    ensures [f]chars_((void *)p, sizeof(unsigned int), _) &*& has_type(p, &typeid(unsigned int)) == true;

lemma_auto void u_integer_to_chars(void *p);
    requires [?f]u_integer(p, _);
    ensures [f]chars(p, sizeof(unsigned int), ?cs) &*& has_type(p, &typeid(unsigned int)) == true;

lemma_auto void short_integer_to_chars(void *p);
    requires [?f]short_integer(p, _);
    ensures [f]chars(p, sizeof(short), ?cs) &*& has_type(p, &typeid(short)) == true;

lemma_auto void u_short_integer_to_chars(void *p);
    requires [?f]u_short_integer(p, _);
    ensures [f]chars(p, sizeof(unsigned short), ?cs) &*& has_type(p, &typeid(unsigned short)) == true;

lemma_auto void pointer_to_chars(void *p);
    requires [?f]pointer(p, ?v);
    ensures [f]chars(p, sizeof(void *), chars_of_pointer(v)) &*& has_type(p, &typeid(void *)) == true;

lemma_auto void boolean_to_chars(void *p);
    requires [?f]boolean(p, _);
    ensures [f]chars(p, sizeof(bool), ?cs) &*& has_type(p, &typeid(bool)) == true;

lemma_auto void integer__to_chars(void *p, int size, bool signed_);
    requires [?f]integer_(p, size, signed_, ?v);
    ensures [f]chars(p, size, _);

// u_character to/from character
lemma_auto void u_character_to_character(void *p);
    requires [?f]u_character(p, _);
    ensures [f]character(p, _);

lemma_auto void character_to_u_character(void *p);
    requires [?f]character(p, _);
    ensures [f]u_character(p, _);

predicate uchars_(unsigned char *p, int count; list<option<unsigned char> > cs) =
    pointer_within_limits(p) == true &*&
    count == 0 ?
        cs == nil
    :
        uchar_(p, ?c) &*& uchars_(p + 1, count - 1, ?cs0) &*& cs == cons(c, cs0);

lemma_auto void uchars__inv();
    requires [?f]uchars_(?p, ?count, ?cs);
    ensures [f]uchars_(p, count, cs) &*& count == length(cs) &*& pointer_within_limits(p) && pointer_within_limits(p + count);

lemma_auto void uchars__split(unsigned char *array, int offset);
   requires [?f]uchars_(array, ?n, ?cs) &*& 0 <= offset &*& offset <= n;
   ensures
       [f]uchars_(array, offset, take(offset, cs))
       &*& [f]uchars_(array + offset, n - offset, drop(offset, cs))
       &*& append(take(offset, cs), drop(offset, cs)) == cs;

lemma_auto void uchars_to_uchars_(unsigned char *array);
    requires [?f]uchars(array, ?n, ?cs);
    ensures [f]uchars_(array, n, map(some, cs));

predicate uchars(unsigned char *p, int count; list<unsigned char> cs) =
    pointer_within_limits(p) == true &*&
    count == 0 ?
        cs == nil
    :
        u_character(p, ?c) &*& uchars(p + 1, count - 1, ?cs0) &*& cs == cons(c, cs0);

lemma_auto void uchars_inv();
    requires [?f]uchars(?p, ?count, ?cs);
    ensures [f]uchars(p, count, cs) &*& count == length(cs) &*& pointer_within_limits(p) && pointer_within_limits(p + count);

lemma_auto void uchars_split(unsigned char *array, int offset);
   requires [?f]uchars(array, ?n, ?cs) &*& 0 <= offset &*& offset <= n;
   ensures
       [f]uchars(array, offset, take(offset, cs))
       &*& [f]uchars(array + offset, n - offset, drop(offset, cs))
       &*& append(take(offset, cs), drop(offset, cs)) == cs;

lemma_auto void uchars_join(unsigned char *array);
    requires [?f]uchars(array, ?n, ?cs) &*& [f]uchars((void *)array + n, ?n0, ?cs0);
    ensures [f]uchars(array, n + n0, append(cs, cs0));

predicate ints_(int *p, int count; list<option<int> > vs) =
    count == 0 ?
        vs == nil
    :
        int_(p, ?v) &*& ints_(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

lemma_auto void ints__split(int *array, int offset);
   requires [?f]ints_(array, ?n, ?vs) &*& 0 <= offset &*& offset <= n;
   ensures
       [f]ints_(array, offset, take(offset, vs))
       &*& [f]ints_(array + offset, n - offset, drop(offset, vs))
       &*& append(take(offset, vs), drop(offset, vs)) == vs;

lemma_auto void ints__join(int *array);
    requires [?f]ints_(array, ?n, ?vs) &*& [f]ints_(array + n, ?n0, ?vs0);
    ensures [f]ints_(array, n + n0, append(vs, vs0));

predicate ints(int *p, int count; list<int> vs) =
    count == 0 ?
        vs == nil
    :
        integer(p, ?v) &*& ints(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

lemma_auto void ints_to_ints_(int *p);
    requires ints(p, ?count, ?vs);
    ensures ints_(p, count, map(some, vs));

lemma_auto void ints__to_ints(int *p);
    requires ints_(p, ?count, ?vs) &*& vs == map(some, map(the, vs));
    ensures ints(p, count, map(the, vs));

lemma_auto void ints_inv();
    requires [?f]ints(?p, ?count, ?vs);
    ensures [f]ints(p, count, vs) &*& count == length(vs);

lemma_auto void ints__inv();
    requires [?f]ints_(?p, ?count, ?vs);
    ensures [f]ints_(p, count, vs) &*& count == length(vs);

predicate uints_(unsigned int *p, int count; list<option<unsigned int> > vs) =
    count == 0 ?
        vs == nil
    :
        uint_(p, ?v) &*& uints_(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

predicate uints(unsigned int *p, int count; list<unsigned int> vs) =
    count == 0 ?
        vs == nil
    :
        u_integer(p, ?v) &*& uints(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

lemma_auto void uints_inv();
    requires [?f]uints(?p, ?count, ?vs);
    ensures [f]uints(p, count, vs) &*& count == length(vs);

predicate longs_(long *p, int count; list<option<long> > ls) =
    count == 0 ?
        ls == nil
    :
        long_(p, ?l) &*& longs_(p + 1, count - 1, ?ls0) &*& ls == cons(l, ls0);

predicate longs(long *p, int count; list<long> ls) =
    count == 0 ?
        ls == nil
    :
        long_integer(p, ?l) &*& longs(p + 1, count - 1, ?ls0) &*& ls == cons(l, ls0);

predicate ulongs_(unsigned long *p, int count; list<option<unsigned long> > ls) =
    count == 0 ?
        ls == nil
    :
        ulong_(p, ?l) &*& ulongs_(p + 1, count - 1, ?ls0) &*& ls == cons(l, ls0);

predicate ulongs(unsigned long *p, int count; list<unsigned long> ls) =
    count == 0 ?
        ls == nil
    :
        ulong_integer(p, ?l) &*& ulongs(p + 1, count - 1, ?ls0) &*& ls == cons(l, ls0);

predicate llongs_(long long *p, int count; list<option<long long> > ls) = 
    count == 0 ?
        ls == nil
    :
        llong_(p, ?l) &*& llongs_(p + 1, count - 1, ?ls0) &*& ls == cons(l, ls0);

predicate llongs(long long *p, int count; list<long long> ls) = 
    count == 0 ?
        ls == nil
    :
        llong_integer(p, ?l) &*& llongs(p + 1, count - 1, ?ls0) &*& ls == cons(l, ls0);

lemma_auto void llongs_inv();
    requires [?f]llongs(?p, ?count, ?vs);
    ensures [f]llongs(p, count, vs) &*& count == length(vs);

predicate ullongs_(unsigned long long *p, int count; list<option<unsigned long long> > ls) = 
    count == 0 ?
        ls == nil
    :
        ullong_(p, ?l) &*& ullongs_(p + 1, count - 1, ?ls0) &*& ls == cons(l, ls0);

predicate ullongs(unsigned long long *p, int count; list<unsigned long long> ls) = 
    count == 0 ?
        ls == nil
    :
        u_llong_integer(p, ?l) &*& ullongs(p + 1, count - 1, ?ls0) &*& ls == cons(l, ls0);

lemma_auto void ullongs_inv();
    requires [?f]ullongs(?p, ?count, ?vs);
    ensures [f]ullongs(p, count, vs) &*& count == length(vs);

predicate shorts_(short *p, int count; list<option<short> > vs) =
    count == 0 ?
        vs == nil
    :
        short_(p, ?v) &*& shorts_(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

predicate shorts(short *p, int count; list<short> vs) =
    count == 0 ?
        vs == nil
    :
        short_integer(p, ?v) &*& shorts(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

lemma_auto void shorts_inv();
    requires [?f]shorts(?p, ?count, ?vs);
    ensures [f]shorts(p, count, vs) &*& count == length(vs);

predicate ushorts_(unsigned short *p, int count; list<option<unsigned short> > vs) =
    count == 0 ?
        vs == nil
    :
        ushort_(p, ?v) &*& ushorts_(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

predicate ushorts(unsigned short *p, int count; list<unsigned short> vs) =
    count == 0 ?
        vs == nil
    :
        u_short_integer(p, ?v) &*& ushorts(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

lemma_auto void ushorts_inv();
    requires [?f]ushorts(?p, ?count, ?vs);
    ensures [f]ushorts(p, count, vs) &*& count == length(vs);

predicate bools_(bool *p, int count; list<option<bool> > vs) =
    count == 0 ?
        vs == nil
    :
        bool_(p, ?v) &*& bools_(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

predicate bools(bool *p, int count; list<bool> vs) =
    count == 0 ?
        vs == nil
    :
        boolean(p, ?v) &*& bools(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

lemma_auto void bools_inv();
    requires [?f]bools(?p, ?count, ?vs);
    ensures [f]bools(p, count, vs) &*& count == length(vs);

predicate intptrs_(intptr_t *p, int count; list<option<intptr_t> > vs) =
    count == 0 ?
        vs == nil
    :
        intptr_(p, ?v) &*& intptrs_(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

predicate uintptrs_(uintptr_t *p, int count; list<option<uintptr_t> > vs) =
    count == 0 ?
        vs == nil
    :
        uintptr_(p, ?v) &*& uintptrs_(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

predicate intptrs(intptr_t *p, int count; list<intptr_t> vs) =
    count == 0 ?
        vs == nil
    :
        intptr(p, ?v) &*& intptrs(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

predicate uintptrs(uintptr_t *p, int count; list<uintptr_t> vs) =
    count == 0 ?
        vs == nil
    :
        uintptr(p, ?v) &*& uintptrs(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

predicate pointers_(void **pp, int count; list<option<void *> > ps) =
    count == 0 ?
        ps == nil
    :
        pointer_(pp, ?p) &*& pointers_(pp + 1, count - 1, ?ps0) &*& ps == cons(p, ps0);

lemma_auto void pointers__inv();
    requires [?f]pointers_(?pp, ?count, ?ps);
    ensures [f]pointers_(pp, count, ps) &*& count == length(ps);

lemma_auto void pointers__split(void **pp, int offset);
    requires [?f]pointers_(pp, ?count, ?ps) &*& 0 <= offset &*& offset <= count;
    ensures [f]pointers_(pp, offset, take(offset, ps)) &*& [f]pointers_(pp + offset, count - offset, drop(offset, ps));

lemma_auto void pointers__join(void **pp);
    requires [?f]pointers_(pp, ?count1, ?ps1) &*& [f]pointers_(pp + count1, ?count2, ?ps2);
    ensures [f]pointers_(pp, count1 + count2, append(ps1, ps2));

lemma_auto void pointers_pointers__join(void **pp);
    requires [?f]pointers(pp, ?count1, ?ps1) &*& [f]pointers_(pp + count1, ?count2, ?ps2);
    ensures [f]pointers_(pp, count1 + count2, append(map(some, ps1), ps2));

predicate pointers(void **pp, int count; list<void *> ps) =
    count == 0 ?
        ps == nil
    :
        pointer(pp, ?p) &*& pointers(pp + 1, count - 1, ?ps0) &*& ps == cons(p, ps0);

lemma_auto void pointers_to_pointers_(void **array);
    requires [?f]pointers(array, ?count, ?ps);
    ensures [f]pointers_(array, count, map(some, ps));

lemma_auto void pointers_inv();
    requires [?f]pointers(?pp, ?count, ?ps);
    ensures [f]pointers(pp, count, ps) &*& count == length(ps);

lemma void pointers_limits(void **array);
    requires [?f]pointers(array, ?n, ?ps) &*& pointer_within_limits(array) == true;
    ensures [f]pointers(array, n, ps) &*& pointer_within_limits(array + n) == true;

lemma_auto void pointers_split(void **pp, int offset);
    requires [?f]pointers(pp, ?count, ?ps) &*& 0 <= offset &*& offset <= count;
    ensures [f]pointers(pp, offset, take(offset, ps)) &*& [f]pointers(pp + offset, count - offset, drop(offset, ps));

lemma_auto void pointers_join(void **pp);
    requires [?f]pointers(pp, ?count1, ?ps1) &*& [f]pointers(pp + count1, ?count2, ?ps2);
    ensures [f]pointers(pp, count1 + count2, append(ps1, ps2));

fixpoint char char_of_uchar(unsigned char c) { return c <= 127 ? c : c - 256; }
fixpoint unsigned char uchar_of_char(char c) { return c < 0 ? c + 256 : c; }

lemma_auto void map_uchar_of_char_char_of_uchar(list<unsigned char> ucs);
    requires true;
    ensures map(uchar_of_char, map(char_of_uchar, ucs)) == ucs;

lemma_auto void map_char_of_uchar_uchar_of_char(list<char> cs);
    requires true;
    ensures map(char_of_uchar, map(uchar_of_char, cs)) == cs;

lemma_auto void chars_to_uchars(void *p);
    requires [?f]chars(p, ?n, ?cs);
    ensures [f]uchars(p, n, map(uchar_of_char, cs));

lemma_auto void chars__to_uchars_(void *p);
    requires [?f]chars_(p, ?n, ?cs);
    ensures [f]uchars_(p, n, map((map_option)(uchar_of_char), cs));

lemma_auto void uchars_to_chars(void *p);
    requires [?f]uchars(p, ?n, ?ucs);
    ensures [f]chars(p, n, map(char_of_uchar, ucs));

lemma_auto void uchars__to_chars_(void *p);
    requires [?f]uchars_(p, ?n, ?ucs);
    ensures [f]chars_(p, n, map((map_option)(char_of_uchar), ucs));

lemma_auto void chars_to_ints(void *p, int n);
    requires [?f]chars(p, n * sizeof(int), _);
    ensures [f]ints(p, n, _);

lemma_auto void ints_to_chars(void *p);
    requires [?f]ints(p, ?n, _);
    ensures [f]chars(p, n * sizeof(int), _) &*& has_type(p, &typeid(int)) == true;

lemma_auto void ints__to_chars_(void *p);
    requires [?f]ints_(p, ?n, _);
    ensures [f]chars_(p, n * sizeof(int), _) &*& has_type(p, &typeid(int)) == true;

lemma_auto void chars_to_uints(void *p, int n);
    requires [?f]chars(p, n * sizeof(unsigned int), _) &*& has_type(p, &typeid(unsigned int)) == true;
    ensures [f]uints(p, n, _);

lemma_auto void uints_to_chars(void *p);
    requires [?f]uints(p, ?n, _);
    ensures [f]chars(p, n * sizeof(unsigned int), _) &*& has_type(p, &typeid(unsigned int)) == true;

lemma_auto void chars_to_bools(void *p, int n);
    requires [?f]chars(p, n * sizeof(bool), _) &*& has_type(p, &typeid(bool)) == true;
    ensures [f]bools(p, n, _);

lemma_auto void bools_to_chars(void *p);
    requires [?f]bools(p, ?n, _);
    ensures [f]chars(p, n * sizeof(bool), _) &*& has_type(p, &typeid(bool)) == true;

fixpoint list<int> integers_of_chars(int size, bool signed_, list<char> cs);
fixpoint list<char> chars_of_integers(int size, bool signed_, list<int> cs);

lemma_auto void chars_to_integers_(void *p, int size, bool signed_, int n);
    requires [?f]chars(p, n * size, ?cs);
    ensures [f]integers_(p, size, signed_, n, integers_of_chars(size, signed_, cs));

lemma_auto void integers__to_chars(void *p);
    requires [?f]integers_(p, ?size, ?signed_, ?n, ?vs);
    ensures
        [f]chars(p, n * size, chars_of_integers(size, signed_, vs)) &*&
        integers_of_chars(size, signed_, chars_of_integers(size, signed_, vs)) == vs;

lemma_auto void integers___to_chars_(void *p);
    requires [?f]integers__(p, ?size, ?signed_, ?n, _);
    ensures [f]chars_(p, n * size, _);

lemma_auto void uchars_to_integers_(void *p, int size, bool signed_, int n);
    requires [?f]uchars(p, n * size, _);
    ensures [f]integers_(p, size, signed_, n, _);

lemma_auto void integers__to_uchars(void *p);
    requires [?f]integers_(p, ?size, ?signed_, ?n, _);
    ensures [f]uchars(p, n * size, _);

lemma_auto void chars__to_pointers_(void *p, int n);
    requires [?f]chars_(p, n * sizeof(void *), _) &*& has_type(p, &typeid(void *)) == true;
    ensures [f]pointers_(p, n, _);

lemma_auto void pointers__to_chars_(void *pp);
    requires [?f]pointers_(pp, ?n, _);
    ensures [f]chars_(pp, n * sizeof(void *), _) &*& has_type(pp, &typeid(void *)) == true;

fixpoint list<void *> pointers_of_chars(list<char> cs);
fixpoint list<char> chars_of_pointers(list<void *> ps);

lemma_auto void chars_to_pointers(void *p, int n);
    requires [?f]chars(p, n * sizeof(void *), ?cs) &*& has_type(p, &typeid(void *)) == true;
    ensures [f]pointers(p, n, pointers_of_chars(cs)) &*& chars_of_pointers(pointers_of_chars(cs)) == cs;

lemma_auto void pointers_to_chars(void *pp);
    requires [?f]pointers(pp, ?n, ?ps) &*& true;
    ensures [f]chars(pp, n * sizeof(void *), chars_of_pointers(ps)) &*& has_type(pp, &typeid(void *)) == true &*& pointers_of_chars(chars_of_pointers(ps)) == ps;

predicate integers__(void *p, int size, bool signed_, int count; list<option<int> > vs) =
    count == 0 ?
        vs == nil
    :
        integer__(p, size, signed_, ?v0) &*& integers__(p + size, size, signed_, count - 1, ?vs0) &*& vs == cons(v0, vs0);

predicate integers_(void *p, int size, bool signed_, int count; list<int> vs) =
    pointer_within_limits(p) == true &*&
    count == 0 ?
        vs == nil
    :
        integer_(p, size, signed_, ?v0) &*& integers_(p + size, size, signed_, count - 1, ?vs0) &*& vs == cons(v0, vs0);

lemma_auto void integers__inv();
    requires [?f]integers_(?p, ?size, ?signed_, ?count, ?vs);
    ensures [f]integers_(p, size, signed_, count, vs) &*& length(vs) == count &*& pointer_within_limits(p + size * count) == true;

lemma void integers__split(void *p, int offset);
    requires [?f]integers_(p, ?size, ?signed_, ?count, ?vs) &*& 0 <= offset &*& offset <= count;
    ensures
        [f]integers_(p, size, signed_, offset, take(offset, vs)) &*&
        [f]integers_(p + size * offset, size, signed_, count - offset, drop(offset, vs)) &*&
        vs == append(take(offset, vs), drop(offset, vs));

lemma void integers__join(void *p);
    requires
        [?f]integers_(p, ?size, ?signed_, ?count1, ?vs1) &*&
        [f]integers_(p + size * count1, size, signed_, ?count2, ?vs2);
    ensures [f]integers_(p, size, signed_, count1 + count2, append(vs1, vs2));

lemma_auto void integers__to_integers__(void *p);
    requires [?f]integers_(p, ?size, ?signed_, ?count, ?vs);
    ensures [f]integers__(p, size, signed_, count, map(some, vs));

predicate floats_(float *p, int count; list<option<float> > values) =
    count == 0 ?
        values == nil
    :
        float__(p, ?value) &*& floats_(p + 1, count - 1, ?values0) &*& values == cons(value, values0);

predicate floats(float *p, int count; list<float> values) =
    count == 0 ?
        values == nil
    :
        float_(p, ?value) &*& floats(p + 1, count - 1, ?values0) &*& values == cons(value, values0);

predicate doubles_(double *p, int count; list<option<double> > values) =
    count == 0 ?
        values == nil
    :
        double__(p, ?value) &*& doubles_(p + 1, count - 1, ?values0) &*& values == cons(value, values0);

predicate doubles(double *p, int count; list<double> values) =
    count == 0 ?
        values == nil
    :
        double_(p, ?value) &*& doubles(p + 1, count - 1, ?values0) &*& values == cons(value, values0);

predicate long_doubles_(long double *p, int count; list<option<long double> > values) =
    count == 0 ?
        values == nil
    :
        long_double_(p, ?value) &*& long_doubles_(p + 1, count - 1, ?values0) &*& values == cons(value, values0);

predicate long_doubles(long double *p, int count; list<long double> values) =
    count == 0 ?
        values == nil
    :
        long_double(p, ?value) &*& long_doubles(p + 1, count - 1, ?values0) &*& values == cons(value, values0);

predicate divrem(int D, int d; int q, int r); // Rounds towards negative infinity, unlike C integer division and remainder.

lemma void divrem_intro(int D, int d, int q, int r);
    requires 0 <= r &*& r < d &*& D == q * d + r;
    ensures [_]divrem(D, d, q, r);

lemma_auto void divrem_elim();
    requires [?f]divrem(?D, ?d, ?q, ?r);
    ensures [f]divrem(D, d, q, r) &*& 0 <= r &*& r < d &*& D == q * d + r;

predicate malloc_block(void *p; int size);
predicate malloc_block_integers_(void *p, int size, bool signed_; int count) = malloc_block(p, ?size_) &*& [_]divrem(size_, size, count, 0);
predicate malloc_block_chars(char *p; int count) = malloc_block(p, count);
predicate malloc_block_uchars(unsigned char *p; int count) = malloc_block(p, count);
predicate malloc_block_ints(int *p; int count) = malloc_block(p, ?size) &*& [_]divrem(size, sizeof(int), count, 0);
predicate malloc_block_uints(unsigned int *p; int count) = malloc_block(p, ?size) &*& [_]divrem(size, sizeof(unsigned int), count, 0);
predicate malloc_block_shorts(short *p; int count) = malloc_block(p, ?size) &*& [_]divrem(size, sizeof(short), count, 0);
predicate malloc_block_ushorts(unsigned short *p; int count) = malloc_block(p, ?size) &*& [_]divrem(size, sizeof(unsigned short), count, 0);
predicate malloc_block_pointers(void **p; int count) = malloc_block(p, ?size) &*& [_]divrem(size, sizeof(void *), count, 0);
predicate malloc_block_intptrs(intptr_t *p; int count) = malloc_block(p, ?size) &*& [_]divrem(size, sizeof(intptr_t), count, 0);
predicate malloc_block_uintptrs(uintptr_t *p; int count) = malloc_block(p, ?size) &*& [_]divrem(size, sizeof(uintptr_t), count, 0);
predicate malloc_block_longs(long *p; int count) = malloc_block(p, ?size) &*& [_]divrem(size, sizeof(long), count, 0);
predicate malloc_block_ulongs(unsigned long *p; int count) = malloc_block(p, ?size) &*& [_]divrem(size, sizeof(unsigned long), count, 0);
predicate malloc_block_llongs(long long *p; int count) = malloc_block(p, ?size) &*& [_]divrem(size, sizeof(long long), count, 0);
predicate malloc_block_ullongs(unsigned long long *p; int count) = malloc_block(p, ?size) &*& [_]divrem(size, sizeof(unsigned long long), count, 0);
predicate malloc_block_bools(bool *p; int count) =  malloc_block(p, ?size) &*& [_]divrem(size, sizeof(bool), count, 0);
predicate malloc_block_floats(float *p; int count) = malloc_block(p, ?size) &*& [_]divrem(size, sizeof(float), count, 0);
predicate malloc_block_doubles(double *p; int count) = malloc_block(p, ?size) &*& [_]divrem(size, sizeof(double), count, 0);
predicate malloc_block_long_doubles(long double *p; int count) = malloc_block(p, ?size) &*& [_]divrem(size, sizeof(long double), count, 0);

@*/

/*@

predicate string(char *s; list<char> cs) =
    character(s, ?c) &*&
    c == 0 ?
        cs == nil
    :
        string(s + 1, ?cs0) &*& cs == cons(c, cs0);

lemma_auto void string_to_body_chars(char *s);
    requires [?f]string(s, ?cs);
    ensures [f]chars(s, length(cs), cs) &*& [f]character(s + length(cs), 0) &*& !mem('\0', cs);

lemma_auto void body_chars_to_string(char *s);
    requires [?f]chars(s, _, ?cs) &*& [f]character(s + length(cs), 0) &*& !mem('\0', cs);
    ensures [f]string(s, cs);

lemma_auto void chars_to_string(char *s);
    requires [?f]chars(s, ?n, ?cs) &*& index_of('\0', cs) == n - 1;
    ensures [f]string(s, take(n - 1, cs));

lemma_auto void string_to_chars_(char *s);
    requires [?f]string(s, ?cs);
    ensures [f]chars_(s, length(cs) + 1, _);

lemma_auto void string_to_chars(char *s);
    requires [?f]string(s, ?cs);
    ensures [f]chars(s, length(cs) + 1, append(cs, cons('\0', nil))) &*& !mem('\0', cs) &*& index_of('\0', append(cs, cons(0, nil))) == length(cs);

lemma_auto void chars_separate_string(char *s);
    requires [?f]chars(s, ?n, ?cs) &*& mem('\0', cs) == true;
    ensures [f]string(s, take(index_of('\0', cs), cs)) &*& [f]chars(s + index_of('\0', cs) + 1, n - index_of('\0', cs) - 1, drop(index_of('\0', cs) + 1, cs));

lemma_auto void chars_unseparate_string(char *s);
    requires [?f]string(s, ?cs) &*& [f]chars(s + length(cs) + 1, ?n, ?cs1);
    ensures [f]chars(s, length(cs) + 1 + n, append(cs, cons('\0', cs1)));

lemma void string_limits(char *s);
    requires [?f]string(s, ?cs);
    ensures [f]string(s, cs) &*& object_pointer_within_limits(s, length(cs) + 1) == true;

inductive vararg =
    vararg_int(int size, int value) // An argument V of signed integer type T is encoded as vararg_int(sizeof(T), V)
  | vararg_uint(int size, unsigned int value)
  | vararg_pointer(void *value)
  | vararg_double(double value);

predicate varargs_(void *lastParam; list<vararg> var_args);

@*/

/*@

// Termination of function pointer calls

fixpoint bool func_lt(void *f, void *g);

predicate call_perm_(int threadId, void *f;);
predicate call_below_perm_(int threadId, void *f;);

@*/

/*@

predicate junk(); // When consuming junk(), VeriFast will consume all chunks in the symbolic heap

predicate module(int moduleId, bool initialState);
predicate module_code(int moduleId;);

predicate argv(char **argv, int argc; list<list<char> > arguments) =
    argc <= 0 ?
        *argv |-> 0 &*& arguments == nil
    :
        *argv |-> ?arg
        &*& string(arg, ?head_arguments)
        &*& argv(argv + 1, argc - 1, ?tail_arguments)
        &*& arguments == cons(head_arguments, tail_arguments); // fix output parameter.
@*/

typedef int main(int argc, char **argv);
    //@ requires 0 <= argc &*& [_]argv(argv, argc, ?arguments);
    //@ ensures junk();

typedef int main_full/*@(int mainModule)@*/(int argc, char **argv);
    //@ requires module(mainModule, true) &*& 0 <= argc &*& [_]argv(argv, argc, ?arguments);
    //@ ensures junk();

// Specify custom_main_spec on your main function to override the main_full default
typedef int custom_main_spec(int argc, char **argv);
    //@ requires false;
    //@ ensures true;

// action permissions

/*@
fixpoint bool is_action_permission0(predicate(box;) p);

lemma void action_permission0_unique(predicate(box;) p, box id);
  requires [?f]p(id) &*& is_action_permission0(p) == true;
  ensures [f]p(id) &*& f <= 1;
  
fixpoint bool is_action_permission1_dispenser<t>(predicate(box, list<t>) p);
fixpoint predicate(box, t) get_action_permission1_for_dispenser<t>(predicate(box, list<t>) p);

lemma void action_permission1_split<t>(predicate(box, list<t>) dispenser, predicate(box, t) p, box id, t x);
  requires is_action_permission1_dispenser(dispenser) == true &*& dispenser(id, ?used) &*& ! mem(x, used) &*& get_action_permission1_for_dispenser(dispenser) == p;
  ensures dispenser(id, cons(x, used)) &*& p(id, x);

lemma void action_permission1_split2<t>(predicate(box, list<t>) dispenser, predicate(box, t) p, box id, t x);
  requires is_action_permission1_dispenser(dispenser) == true &*& dispenser(id, ?used) &*& ! mem(x, used) &*& get_action_permission1_for_dispenser(dispenser) == p;
  ensures dispenser(id, append(used, cons(x, nil))) &*& p(id, x);

lemma void action_permission1_merge<t>(predicate(box, list<t>) dispenser, predicate(box, t) p, box id, t x);
  requires is_action_permission1_dispenser(dispenser) == true &*& dispenser(id, ?used) &*& get_action_permission1_for_dispenser(dispenser) == p &*& p(id, x);
  ensures dispenser(id, remove(x, used));
  
fixpoint bool is_action_permission1<t>(predicate(box, t;) p);

lemma void action_permission1_unique<t>(predicate(box, t;) p, box id, t x);
  requires [?f]p(id, x) &*& is_action_permission1<t>(p) == true;
  ensures [f]p(id, x) &*& f <= 1;
  
predicate is_handle(handle ha);

lemma void is_handle_unique(handle ha1, handle ha2);
  requires is_handle(ha1) &*& is_handle(ha2);
  ensures is_handle(ha1) &*& is_handle(ha2) &*& ha1 != ha2;

lemma void box_level_unique(box id1, box id2);
  requires id1 != id2;
  ensures box_level(id1) != box_level(id2);

fixpoint real box_level(box id);

predicate current_box_level(real level);
@*/

/*@

// Fixpoint operator, for defining functions by well-founded recursion over the nonnegative integers

fixpoint b fix<a, b>(fixpoint(fixpoint(a, b), a, b) def, fixpoint(a, int) measure, a x);

// A proof of this lemma is in examples/wf_func_proof.c

lemma void fix_unfold<a, b>(fixpoint(fixpoint(a, b), a, b) def, fixpoint(a, int) measure, a x0);
    requires 0 <= measure(x0) && fix(def, measure, x0) != def((fix)(def, measure), x0);
    ensures
        exists<pair<pair<fixpoint(a, b), fixpoint(a, b)>, a> >(pair(pair(?f1, ?f2), ?a)) &*&
        forall_(a x; measure(x) < 0 || measure(a) <= measure(x) || f1(x) == f2(x)) &*&
        0 <= measure(a) &*&
        def(f1, a) != def(f2, a);

@*/

#endif
