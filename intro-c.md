# VeriFast for C

[VeriFast](https://github.com/verifast/verifast) is a tool for verifying the
absence of [undefined
behavior](https://blog.regehr.org/archives/213)
in single-threaded or multithreaded C programs. VeriFast performs *modular
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
programs involving pointers, different expressions can denote the
same variable. By enabling assertions to express exclusive *ownership* of
memory regions, separation logic enables concise specifications, proper
information hiding, and efficient verification for pointer-manipulating
programs.

## An example

Consider, for example, the function `reverse_in_place` below that reverses the
given linked list in-place and returns a pointer to the first node (which
was the originally the last node).

```c
struct node {
    struct node *next;
};

/*@

predicate nodes(struct node *n; list<struct node *> nodes) =
    n == 0 ?
        nodes == nil
    :
        n->next |-> ?next &*& nodes(next, ?nodes0) &*& nodes == cons(n, nodes0);

@*/

struct node *reverse_in_place(struct node *n)
//@ requires nodes(n, ?nodes);
//@ ensures nodes(result, reverse(nodes));
{
    struct node *m = 0;
    for (;;)
    //@ invariant nodes(n, ?n_nodes) &*& nodes(m, ?m_nodes) &*& reverse(nodes) == append(reverse(n_nodes), m_nodes);
    {
        //@ open nodes(n, _);
        if (n == 0) {
            return m;
        }
        struct node *k = n->next;
        //@ append_assoc(reverse(tail(n_nodes)), {n}, m_nodes);
        n->next = m;
        m = n;
        n = k;
    }
}
```

VeriFast interprets comments of the form `/*@ ... @*/` or `//@ ...` as VeriFast annotations. This example illustrates four types of annotations:
- Two *specification clause annotations* specify the function's precondition and postcondition, respectively.
- The precondition and postcondition are specified in terms of the separation logic predicate `nodes`, defined in a *ghost declaration annotation*. This predicate
  recursively defines the memory footprint of the linked list starting at a given node `n` and associates it with a mathematical list `nodes` of node locations.
  The separating conjunction `&*&` implies that the first node of the linked list is *separate* from the remainder of the linked list. It follows that mutating the first node does not affect
  the remainder of the linked list. The *variable pattern* `?next` binds logical variable `next` to the value of field `n->next`; its scope extends to the end of the assertion.
  If a logical variable is introduced in a precondition, its scope includes the postcondition.
- A *loop header annotation* specifies the loop invariant, expressing that `n` and `m` point to disjoint linked lists and expressing the relationship between their contents and that of the original linked list.
- *Ghost command annotations* provide hints needed for the symbolic execution algorithm to succeed. `open nodes(n, _)` unfolds the `nodes` predicate application whose first argument equals `n`. `append_assoc` invokes a library *lemma* expressing the associativity of the `append` operation on mathematical lists.

The generic mathematical datatype `list` is defined in file [`list.gh`](https://github.com/verifast/verifast/blob/master/bin/list.gh), part of VeriFast's *prelude*, as follows:
```
inductive list<t> = nil | cons(t, list<t>);
```
A list of `t` values is either empty, denoted by *constructor* `nil`, or nonempty, with first element (or *head*) `v` and remainder (or *tail*) `vs`, denoted by `cons(v, vs)`.

Mathematical functions `append` and `reverse` are defined in the same file as follows:
```
fixpoint list<t> append<t>(list<t> xs, list<t> ys) {
    switch (xs) {
        case nil: return ys;
        case cons(x, xs0): return cons(x, append(xs0, ys));
    }
}

fixpoint list<t> reverse<t>(list<t> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x, xs0): return append(reverse(xs0), cons(x, nil));
    }
}
```
Lemma `append_assoc` is declared (but not proven) in the same file. Here is a proof:
```
lemma void append_assoc<t>(list<t> xs, list<t> ys, list<t> zs)
    requires true;
    ensures append(append(xs, ys), zs) == append(xs, append(ys, zs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            append_assoc(xs0, ys, zs);
    }
}
```
A lemma is like a regular Rust function, except that it is declared inside an annotation. VeriFast checks that it has no side effects and that it terminates.

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
complexities of the verification task. Specifically, you can tell VeriFast to ignore arithmetic overflow, ignore effective types (in other words, assume the presence of gcc's `-fno-strict-aliasing` flag), or ignore pointer provenance (or only subobject provenance).  All of these options can also be
specified on the command line.

## Further reading

- [The VeriFast Tutorial](https://doi.org/10.5281/zenodo.887906)
