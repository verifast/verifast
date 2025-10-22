# A brief introduction to VeriFast for Rust

[VeriFast](https://github.com/verifast/verifast) is a tool for verifying the
absence of [undefined
behavior](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)
in single-threaded or multithreaded Rust programs that use `unsafe` blocks, and
for verifying
[soundness](https://doc.rust-lang.org/nomicon/working-with-unsafe.html) of Rust
crates/modules that use `unsafe` blocks. VeriFast performs *modular
verification*: it verifies one function at a time; during the verification of
one function, if that function calls another function, VeriFast uses the
callee's *specification*, not its implementation, to reason about the call.
VeriFast verifies each function against its specification: it verifies that, if
started in a state that satisfies the precondition, the function does not have
undefined behavior and any state in which it returns satisfies the
postcondition.

Besides requiring that the user annotate each function with a precondition and
a postcondition, VeriFast also requires that the user annotate each loop with a
loop invariant. This enables its modular symbolic execution algorithm to
perform only a single symbolic execution of the loop's body to cover all
possible real executions of the loop. Furthermore, the use of function
specifications means a single symbolic execution of a function covers all
possible real executions, even if the function is recursive. In summary, these
annotations enable VeriFast to perform unbounded verification (i.e. of
arbitrarily long, including infinitely long, executions) in finite time.

VeriFast function specifications and loop invariants are expressed in a form of
[*separation logic*](https://en.wikipedia.org/wiki/Separation_logic), and it
performs symbolic execution using a separation logic-based representation of
memory. Separation logic addresses the problem of *aliasing*, which is that in
programs involving pointers or references, different expressions can denote the
same variable. By enabling assertions to express exclusive *ownership* of
memory regions, separation logic enables concise specifications, proper
information hiding, and efficient verification for pointer-manipulating
programs.

## Verifying `unsafe` functions

Consider, for example, the function `Node::reverse_in_place` below that reverses the
given linked list in-place and returns a pointer to the first node (which
was the originally the last node).

```rust
struct Node {
    next: *mut Node,
}

/*@

pred Nodes(n: *mut Node; nodes: list<*mut Node>) =
    if n == 0 {
        nodes == nil
    } else {
        (*n).next |-> ?next &*& Nodes(next, ?nodes0) &*& nodes == cons(n, nodes0)
    };

@*/

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ req Nodes(n, ?nodes);
    //@ ens Nodes(result, reverse(nodes));
    //@ on_unwind_ens false;
    {
        let mut m = std::ptr::null_mut();
        loop {
            //@ inv Nodes(n, ?n_nodes) &*& Nodes(m, ?m_nodes) &*& reverse(nodes) == append(reverse(n_nodes), m_nodes);
            //@ open Nodes(n, _);
            if n.is_null() {
                return m;
            }
            let k = (*n).next;
            //@ append_assoc(reverse(tail(n_nodes)), [n], m_nodes);
            (*n).next = m;
            m = n;
            n = k;
        }
    }

}
```

VeriFast interprets comments of the form `/*@ ... @*/` or `//@ ...` as VeriFast annotations. This example illustrates four types of annotations:
- Three *specification clause annotations* specify the function's precondition, postcondition, and unwind postcondition, respectively. The function never unwinds, so its
  unwind postcondition is `false`.
- The precondition and postcondition are specified in terms of the separation logic predicate `Nodes`, defined in a *ghost declaration annotation*. This predicate
  recursively defines the memory footprint of the linked list starting at a given node `n` and associates it with a mathematical list `nodes` of node locations.
  The separating conjunction `&*&` implies that the first node of the linked list is *separate* from the remainder of the linked list. It follows that mutating the first node does not affect
  the remainder of the linked list. The *variable pattern* `?next` binds logical variable `next` to the value of field `(*n).next`; its scope extends to the end of the assertion.
  If a logical variable is introduced in a precondition, its scope includes the postcondition.
- At the start of the loop body, a *block annotation* specifies the loop invariant, expressing that `n` and `m` point to disjoint linked lists and expressing the relationship between their contents and that of the original linked list.
- *Ghost command annotations* provide hints needed for the symbolic execution algorithm to succeed. `open Nodes(n, _)` unfolds the `Nodes` predicate application whose first argument equals `n`. `append_assoc` invokes a library *lemma* expressing the associativity of the `append` operation on mathematical lists.

The generic mathematical datatype `list` is defined in file [`list.rsspec`](https://github.com/verifast/verifast/blob/master/bin/rust/list.rsspec), part of VeriFast's *prelude*, as follows:
```
inductive list<t> = nil | cons(t, list<t>);
```
A list of `t` values is either empty, denoted by *constructor* `nil`, or nonempty, with first element (or *head*) `v` and remainder (or *tail*) `vs`, denoted by `cons(v, vs)`.

Mathematical functions `append` and `reverse` are defined in the same file as follows:
```
fix append<t>(xs: list<t>, ys: list<t>) -> list<t> {
    match xs {
        nil => ys,
        cons(x, xs0) => cons(x, append(xs0, ys))
    }
}

fix reverse<t>(xs: list<t>) -> list<t> {
    match xs {
        nil => nil,
        cons(x, xs0) => append(reverse(xs0), cons(x, nil))
    }
}
```
Lemma `append_assoc` is declared (but not proven) in the same file. Here is a proof:
```
lem append_assoc<t>(xs: list<t>, ys: list<t>, zs: list<t>)
    req true;
    ens append(append(xs, ys), zs) == append(xs, append(ys, zs));
{
    match xs {
        nil => {}
        cons(x, xs0) => {
            append_assoc(xs0, ys, zs);
        }
    }
}
```
A lemma is like a regular Rust function, except that it is declared inside an annotation. VeriFast checks that it has no side effects and that it terminates.

## Verifying safe abstractions

Consider the following broken implementation of [`std::mem::replace`](https://doc.rust-lang.org/std/mem/fn.replace.html):
```rust
fn replace<T>(dest: &mut T, src: T) -> T {
    unsafe {
        let result = (dest as *mut T).read();
        (dest as *mut T).write(src);
        (dest as *mut T).read() // should be `result`
    }
}
```
The Rust compiler accepts it just fine, but VeriFast complains that it cannot prove that when this function returns, the ownership of the value pointed to by `dest` is *separate* from the ownership of the return value. If we replace the final line by `result`, VeriFast accepts the code.

For a function not marked as `unsafe`, VeriFast generates a specification expressing that the function is *semantically well-typed* per [RustBelt](https://research.ralfj.de/thesis.html)'s definition of what Rust's types mean in separation logic. If no specification clause annotations are provided for the function, VeriFast verifies the function against the generated specification; otherwise, VeriFast first verifies that the provided specification implies the generated one, and then verifies the function against the provided specification.

The generated specification for `replace` is as follows:
```rust
fn replace<T>(dest: &mut T, src: T) -> T
//@ req thread_token(?_t) &*& *dest |-> ?dest0 &*& <T>.own(_t, dest0) &*& <T>.own(_t, src) &*& _t == currentThread;
//@ ens thread_token(_t) &*& *dest |-> ?dest1 &*& <T>.own(_t, dest1) &*& <T>.own(_t, result);
```
`<T>.own(t, v)` expresses ownership of the T value `v` accessible to thread `t` (in case T is not [Send](https://doc.rust-lang.org/nomicon/send-and-sync.html)).
`thread_token(t)` represents permission to open *nonatomic invariants* and *nonatomic borrows* at thread `t`; these contain resources shared in a non-thread-safe way at thread `t`.

For more information on how to verify safe abstractions in VeriFast, see the relevant [chapter](https://verifast.github.io/verifast/rust-reference/non-unsafe-funcs.html) in the VeriFast for Rust Reference and the [examples](https://github.com/verifast/verifast/tree/master/tests/rust/safe_abstraction) (in `tests/rust/safe_abstraction` in the VeriFast binary distributions). (See [`testsuite.mysh`](https://github.com/verifast/verifast/blob/master/tests/rust/testsuite.mysh) to learn the command line to use to verify a particular example.)

## Running VeriFast

To run VeriFast, download a binary distribution for your platform, either the
[nightly build](https://github.com/verifast/verifast/releases/tag/nightly) or
the [latest named
release](https://github.com/verifast/verifast/releases/latest). Extract the
archive to any folder on your computer. (On Macs, first [remove the quarantine
bit](https://github.com/verifast/verifast?tab=readme-ov-file#binaries).) Then,
either use the VeriFast IDE at `bin/vfide`, the command-line tool at
`bin/verifast`, or the [VSCode
extension](https://marketplace.visualstudio.com/items?itemName=VeriFast.verifast).
In the IDE, open a file and press F5 to verify it. VeriFast will then either
report "0 errors found" or show a debugger-like GUI that allows you to step
through the failed symbolic execution path and inspect the symbolic state at
each step. If verification succeeds, choose Show execution tree to see the tree
of symbolic execution paths traversed for each function that was verified.

In the IDE, the Verify menu allows you to postpone dealing with certain
complexities of the verification task. Specifically, you can tell VeriFast to
ignore unwind paths, ignore arithmetic overflow, and treat shared reference
creation like raw pointer creation (which ignores the complexities of Rust's
[pointer aliasing
rules](https://marketplace.visualstudio.com/items?itemName=VeriFast.verifast)).
(Many of the other options are only relevant when verifying C programs and have
no effect when verifying Rust programs.) All of these options can also be
specified on the command line.

## Further reading

- [A tour of the RawVec proof](tests/rust/safe_abstraction/raw_vec/)
- [A tour of the LinkedList proof](tests/rust/safe_abstraction/linked_list/)
- [Verifying purely `unsafe` Rust programs with VeriFast: a tutorial](https://zenodo.org/records/17413725)
- [The VeriFast for Rust Reference](https://verifast.github.io/verifast/rust-reference)