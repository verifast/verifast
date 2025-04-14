# Verifying compliance with Rust's pointer aliasing rules

Breaking [Rust's pointer aliasing
rules](https://doc.rust-lang.org/reference/behavior-considered-undefined.html#r-undefined.alias)
or mutating [immutable
bytes](https://doc.rust-lang.org/reference/behavior-considered-undefined.html#r-undefined.immutable)
is undefined behavior. VeriFast currently verifies (only) the latter.

In particular, it verifies that the memory pointed to by a shared reference,
except for the memory inside an `UnsafeCell`, is not mutated while the shared
reference is active. First of all, shared reference creation is treated like the
creation of a new pointer value, with the same address but a different
[provenance](https://doc.rust-lang.org/std/ptr/index.html#provenance) from the
original pointer. Points-to resources for the original pointer cannot be used
for accesses through the new shared reference.

VeriFast requires, at creation of a shared reference, that the user transfer a
fraction greater than 0 and less than 1 of the points-to resources for the
original place to the new shared reference. These resources are transferred back
to the original reference when the shared reference is *ended* (and only then);
from that point on, the shared reference is no longer usable.

Specifically, a shared reference creation expression `&E` is treated like a call
of function `create_ref` in
[`aliasing.rsspec`](https://github.com/verifast/verifast/blob/master/bin/rust/aliasing.rsspec),
which is part of the VeriFast for Rust prelude. This function requires that a
shared reference value has been *precreated* using lemma `precreate_ref`
declared in the same file. Furthermore, it requires that the new reference has
been *initialized*.

Memory inside an `UnsafeCell` is exempted from this process; the points-to
resources for that memory are never transferred. This means that a shared
reference to an `UnsafeCell` does not directly provide access to the memory
behind the `UnsafeCell`. To access the memory, the developer has to call
`UnsafeCell::get`. VeriFast treats calls of this method like calls of logical
function `ref_origin` (also declared in `aliasing.rsspec`). Therefore, if a
struct S has a field f of type `UnsafeCell<T>` inside, it is important for
`<S>.share(k, t, l)` to (directly or indirectly, e.g. via a nonatomic borrow),
assert points-to resources for `ref_origin(&(*l).f)`. See, for example,
[cell.rs](https://github.com/verifast/verifast/blob/master/tests/rust/safe_abstraction/cell.rs)
and
[mutex.rs](https://github.com/verifast/verifast/blob/master/tests/rust/safe_abstraction/mutex.rs).