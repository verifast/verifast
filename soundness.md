C Programs
==========

Target soundness statement:
If `verifast A.c B.c C.c` succeeds, then `gcc -o ./program.exe A.c B.c C.c && ./program.exe` does not throw any assertion failures.

Known VeriFast unsoundnesses:
- The lemma `mutex_ghost_use` (declared in `bin/threading.h`) is unsound. For example, it can be called after a `mutex_acquire` call, causing re-entry. A version for locks that requires that the lock be below the current thread's lockset would be sound.
- We currently assume the same macros are defined on the command line when verifying the various modules that include a particular header file. (Otherwise, different modules may interpret the same header file differently.) TODO: Record the defined macros in the .vfmanifest?
- predicate preciseness analysis: does not deal correctly with the local variable scopes induced by conditional assertions and switch assertions
- disallow the use of regular function pointers as predicate family indices in unloadable modules. (Note: using lemma function pointers as predicate family indices is fine.)
- VeriFast assumes that the C compiler does not assume that the C program obeys strict aliasing rules.
  For example, `gcc -O2` assumes that a pointer-to-float does not alias a pointer-to-int, and therefore that an assignment through one of these
  does not affect the value at the other location.
  VeriFast does not check that the program obeys strict aliasing rules. Therefore, VeriFast is currently unsound for `gcc -O2`.
  However, this unsoundness does not apply to `gcc -O2 -fno-strict-aliasing`.
- The C standard says that reading an uninitialized variable or using the value so obtained can cause a trap. VeriFast does not check that the program does not read or use uninitialized variables.
- I am not 100% sure that a statement of the form `x = foo();` where x is a global and foo modifies x is allowed by the C standard. VeriFast allows this statement.
- The pointer arithmetic implied by field or array dereference should be checked for arithmetic overflow. For example, the following program verifies, even though
  the `assert(false);` is reachable:

```c
struct bar { int x; int y; };

void foo()
  //@ requires true;
  //@ ensures true;
{
  void *p0 = 0;
  void *q0 = &((struct bar *)p0)->y;
  //@ produce_limits(q0);
  //@ assert p0 <= q0;
  //@ assert q0 - p0 >= 0;
  void *p = (void *)UINTPTR_MAX;
  void *q = &((struct bar *)p)->y;
  //@ produce_limits(q);
  //@ assert q <= p;
  //@ assert q - p <= 0;
  //@ assert q - p == 0;
  struct bar b;
  //@ open bar_x(&b, _);
  //@ open bar_y(&b, _);
  //@ integer_distinct(&b.x, &b.x);
  assert(false);
}
```

Java Programs
=============

Target soundness statement:
If `javac A.java B.java C.java` succeeds, and `program.jarsrc` contains the following lines:

```
A.java
B.java
C.java
main-class A
```

and `verifast -c program.jarsrc` succeeds, then `java A` does not throw any assertion failures.

Known VeriFast unsoundnesses:
- Java: ClassCastExceptions are currently not prevented
- ghost variables (which can hide fields) can appear in the argument of the Java assert statement
- Spec of Selector.selectedKeys: states that the selected-keys set does not contain any cancelled keys. This is not true.
- API specs: Not all specs of methods that throw checked exceptions (such as IOException) declare them
- Linking soundness (i.e. soundness for multi-jar programs) has not yet been thoroughly dealt with
- See tests/bugs/z3-proves-false.java. Reduced test case at tests/bugs/z3-proves-false/z3-proves-false.java. This seems to be an unsoundness in Z3 1.3.6, but further research is necessary.
