# The lifetime logic

Here, we introduce our [encoding](https://github.com/verifast/verifast/blob/master/bin/rust/rust_belt/lifetime_logic.rsspec) into VeriFast of Jung et al.'s [lifetime logic](https://research.ralfj.de/thesis.html), a library of separation logic constructs for expressing what it means in separation logic to own a mutable reference or a shared reference. More specifically, it enables defining a separation logic predicate `<T>.own` for each Rust type T such that `<T>.own(v)` expresses ownership of Rust value `v` of type `T` and such that a separation logic specification expressing semantic well-typedness of a Rust function `f` can be written as follows:
```rust
fn f(p1: T1, p2: T2) -> U
//@ req <T1>.own(p1) &*& <T2>.own(p2);
//@ ens <U>.own(result);
```
This specification expresses that the caller must pass ownership of argument values `p1` and `p2` into the function, and that the function must pass ownership of the return value to the caller when it returns. In other words, it expresses that the function is allowed to *consume* ownership of the argument values and is required to *produce* ownership of the result value.

(Note: for now, we ignore the fact that some Rust values (of non-Send types) are accessible only to particular threads.)

## Mutable references

Consider the following example program:
```rust
fn increment(r: &mut i32) { *r += 1; }

fn main() {
    let x = 83;
    increment(&mut x);
    x /= 2;
    println!("The answer is {}", x);
}
```
We can verify safety of this program in VeriFast trivially as follows:
```rust
fn increment(r: &mut i32)
//@ req *r |-> ?v0;
//@ ens *r |-> ?v1;
{ *r += 1; }

fn main()
//@ req true;
//@ ens true;
{
    let x = 83;
    increment(&mut x);
    x /= 2;
    println!("The answer is {}", x);
}
```
The specification for `increment` requires that the caller pass exclusive ownership of the place referred to by `r` into the function, and requires the function to pass it back to the caller when it returns.

Notice, however, that this specification is not of the form that we are looking for: we are looking for a definition for `<&mut i32>.own` such that the specification for `increment` can be written roughly as
```rust
fn increment(r: &mut i32)
//@ req <&mut i32>.own(r);
//@ ens true;
```
That is, it should be sufficient for the caller to pass ownership of the mutable reference into the function, without the function
passing any resources related to `r` back to the caller! But if the function cannot pass anything back, how can the caller get the permissions it needs to perform `x /= 2;`?

To solve this conundrum, it is crucial to remember that Rust associates a *lifetime* with each mutable reference. The full type of function `increment` is as follows:
```rust
fn increment<'a>(r: &'a mut i32)
```
The mutable reference is valid only until the end of lifetime `'a`. Only after `'a` has ended, can the caller again mutate the place. So ownership of a mutable reference should express the exclusive ownership of the place referred to by the reference, but only until the end of the associated lifetime.

This is exactly what is expressed by lifetime logic predicate `full_borrow`: `full_borrow(k, p)` expresses exclusive ownership of the resources described by predicate value `p`, but only until the end of lifetime `k`. We therefore define `<&'a mut T>.own(l) = full_borrow('a, <T>.full_borrow_content(l))` where `<T>.full_borrow_content` is a *predicate constructor* that, when applied to argument list `(l)`, constructs a predicate value `<T>.full_borrow_content(l)`. Applying this predicate value to an empty argument list, in turn, asserts ownership of the place referred to by `l`, as well as ownership of the value stored at that place: `<T>.full_borrow_content(l)() = *l |-> ?v &*& <T>.own(v)`.

We obtain the following specification for `increment`:
```rust
fn increment<'a>(r: &'a mut i32)
//@ req [?qa]lifetime_token('a) &*& <&'a mut i32>.own(r);
//@ ens [qa]lifetime_token('a);
```
The assertion `[qa]lifetime_token('a)` asserts *fractional ownership* of the *lifetime token* for lifetime `'a`. The *coefficient* `qa` is a real number greater than 0 and not greater than 1. Starting a lifetime creates the lifetime token for that lifetime, and ending the lifetime destroys the token. Therefore, fractional ownership of the lifetime token for a lifetime guarantees that the lifetime is alive (i.e. that it has started and has not yet ended). The notation `?qa` binds the coefficient to logical variable `qa`; the specification requires that the caller pass a fraction of the lifetime token for `'a` to the function, and that the function pass the same fraction back to the caller when it returns.

Given this specification, we can verify function `increment` as follows:
```rust
fn increment<'a>(r: &'a mut i32)
//@ req [?qa]lifetime_token('a) &*& full_borrow('a, <i32>.full_borrow_content(r));
//@ ens [qa]lifetime_token('a);
{
    //@ open_full_borrow(qa, 'a, <i32>.full_borrow_content(r));
    //@ open <i32>.full_borrow_content(r)();
    *r += 1;
    //@ close <i32>.full_borrow_content(r)();
    //@ close_full_borrow(<i32>.full_borrow_content(r));
    //@ leak full_borrow('a, <i32>.full_borrow_content(r));
}
```
The proof uses lemma [`open_full_borrow`](https://github.com/verifast/verifast/blob/c0c90ac3a094c3efa914aa219f66e727e1104d08/bin/rust/rust_belt/lifetime_logic.rsspec#L135). `open_full_borrow(q, k, p)` consumes `full_borrow(k, p)` and `[q]lifetime_token(k)` and produces `p()` as well as `close_full_borrow_token(p, q, k)`. The latter can later be passed to lemma [`close_full_borrow`](https://github.com/verifast/verifast/blob/c0c90ac3a094c3efa914aa219f66e727e1104d08/bin/rust/rust_belt/lifetime_logic.rsspec#L140) to recover the lifetime token fraction `[qa]lifetime_token(k)`. `close_full_borrow(k, p)` consumes `close_full_borrow_token(p, q, k)` and `p()`, for some `q`, and produces `[q]lifetime_token(k)`. After closing the full borrow, the proof can leak it, since it is no longer needed.

The main function can then be verified as follows:
```rust
fn main()
//@ req true;
//@ ens true;
{
    let mut x = 83;
    //@ let k = begin_lifetime();
    //@ close <i32>.full_borrow_content(&x)();
    //@ borrow(k, <i32>.full_borrow_content(&x));
    {
        //@ let_lft 'a = k;
        increment/*@::<'a>@*/(&mut x);
    }
    //@ end_lifetime(k);
    //@ borrow_end(k, <i32>.full_borrow_content(&x));
    //@ open <i32>.full_borrow_content(&x)();
    x /= 2;
    println!("The answer is {}", x);
}
```
The proof starts a lifetime `k`, obtaining `[1]lifetime_token(k)`. It then creates a full borrow of `&x` at `k` and binds semantic lifetime `k` to type system lifetime variable `'a` using a `let_lft` declaration, so that it can call `increment` with lifetime generic parameter `'a` bound to lifetime variable `'a`. After the call returns, the proof can end the lifetime using lemma [`end_lifetime`](https://github.com/verifast/verifast/blob/c0c90ac3a094c3efa914aa219f66e727e1104d08/bin/rust/rust_belt/lifetime_logic.rsspec#L76), which produces `[_]lifetime_dead_token(k)`. That token can be used to end the full borrow with [`borrow_end`](https://github.com/verifast/verifast/blob/c0c90ac3a094c3efa914aa219f66e727e1104d08/bin/rust/rust_belt/lifetime_logic.rsspec#L122) and recover exclusive ownership of `x`.

## Shared references

[TODO]