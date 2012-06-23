Welcome to the VeriFast codebase
================================

Outline of the codebase
-----------------------

The core of the codebase is in the following files, to be read in this order:

util.ml -- Utility functions on lists, strings, etc.
stats.ml -- Statistics
lexer.ml -- The lexer
ast.ml -- The AST, plus some functions for converting to a string, for getting the location, for folding and iteration over an AST, etc.
parser.ml -- The parser
verifast0.ml -- Some basic definitions, such as 'heap', 'env', 'context'
verifast1.ml -- Some global state, type checker, evaluation of pure expressions
assertions.ml -- Production and consumption of assertions, automation rules
verify_expr.ml -- Symbolic execution of side-effecting expressions
verifast.ml -- Symbolic execution of statements, blocks, functions, classes

(Note: when using Notepad++, open all files and use 'File->Save Session...'.
Save the session as 'verifast.nppsession'. In Settings->Preferences->Misc,
set 'Session file ext.' to 'nppsession'. Then add verifast.nppsession to your
Start menu. Use Ctrl+F->Find in All Opened Documents.)

Frontends:

vfconsole.ml -- The command-line tool (verifast.exe)
vfide.ml -- The IDE (vfide.exe)

Backends:

proverapi.ml -- Common API used by the core to access the SMT solver (Z3/Redux)
z3prover.ml -- Implements the prover API using Microsoft's Z3 SMT solver (version 1.3.6)
redux.ml -- A simple SMT solver developed in-house (a partial re-implementation of the Simplify SMT solver by Detlefs, Nelson, Saxe; see their TR HPL-2003-148)
simplex.ml -- A partial re-implementation of the Simplex module for checking satisfiability of systems of linear inequations over the rationals (see TR HPL-2003-148)

Assertion plugins: (An experimental feature that allows users to plug in their own kinds of assertions; see examples/plugins.)

DynType.ml -- offers a form of dynamic typing with downcasts
plugins.ml
plugins_private.ml
plugins2.ml

Structure of the core codebase
------------------------------

The core of the verifier can be thought of as a huge function
'verify_program_core' that takes the file name of a .c or .java (or .jarsrc)
file and either returns '()' if verification succeeds or throws an
exception if verification fails. The most common exceptions are
ParseException, StaticError, and SymbolicExecutionError. The latter
carries a symbolic execution trace as an argument.

The body of function 'verify_program_core' is spread out over files
verifast1.ml, assertions.ml, verify_expr.ml, and verifast.ml. Since
you can't really spread an OCaml function definition over multiple
files, the function's body has been turned into an OCaml module, and
this module has been split into four chunks.

More specifically, verifast1.ml defines a module (actually, a functor,
i.e. a parameterized module) VerifyProgram1. assertions.ml defines a
module Assertions, that includes VerifyProgram1 and adds some more
definitions. verify_expr.ml defines a module VerifyExpr that includes
Assertions. Finally, verifast.ml defines a module VerifyProgram that
includes VerifyExpr.

The actual function 'verify_program_core', defined at the bottom of
verifast.ml, instantiates module VerifyProgram (which is actually
a functor). The actual verification happens as a side-effect of the
instantiation of VerifyProgram.

A wheel within a wheel: check_file
----------------------------------

Q. What is the internal structure of 'verify_program_core'
(i.e. module VerifyProgram, with its includes)?

A. 90% of 'verify_program_core' consists of a nested function 'check_file'.
This function takes as input the name of a .c, .jarsrc, .h, or .jarspec
file, and returns typechecked versions of the elements defined in the input
file. 'check_file' for a .c (or .h) file recursively calls 'check_file' for
the .h files included by the input file. 'check_file' also verifies any
function bodies it encounters in the input file, and throws an exception
if verification fails.

Like 'verify_program_core', 'check_file' is spread over the files
verifast1.ml, assertions.ml, verify_expr.ml, and verifast.ml. More
specifically, module VerifyProgram1 in verifast1.ml defines a nested
module (actually, a functor) CheckFile1. Module Assertions in assertions.ml
defines a nested module CheckFile_Assertions that includes CheckFile1. Module
VerifyExpr in verify_expr.ml defines a nested module CheckFile_VerifyExpr that
includes CheckFile_Assertions. Finally, module VerifyProgram in verifast.ml
defines a nested module CheckFile that includes CheckFile_VerifyExpr. The actual
function 'check_file', defined at the bottom of module VerifyProgram, simply
instantiates module CheckFile and returns its member 'result'.


How to understand this codebase?
================================

- Understand the VeriFast verification approach.
  - Master VeriFast as a user. See the VeriFast Tutorial ("The VeriFast Program Verifier: A Tutorial") on the VeriFast website.
    - [TODO: Not all topics are introduced in the tutorial yet. Add more topics.]
  - Understand the theory behind VeriFast.
    - The core theory is explained in the Featherweight VeriFast work by Frederic Vogels (see his PhD thesis).
    - [TODO: Formalize more aspects of VeriFast.]

- This program is written in OCaml. Know OCaml.
  See the manual at http://caml.inria.fr/. The manual includes:
  - Part I: An introduction to OCaml (not great; also Google "OCaml tutorial")
  - Part II: The OCaml language (A fairly complete but very terse language reference)
  - Part III: The OCaml tools (The compiler)
  - Part IV: The OCaml library (The core library (= the built-ins, including print_endline), the standard library (including List and String), etc.)
  Familiarize yourself with the precedence of operators.
  Caveats:
  - Subexpression evaluation order is unspecified. Use let x = ... in ... to enforce ordering.
  - 'begin ... end' is alternative syntax for '(...)'. Coding guideline: use 'begin ... end' for multiline expressions.
  - 'if ... then ...; ...' parses as '(if ... then ...); ...'. To fix: 'if ... then begin ...; ... end'
  - OCaml supports structural equality 'x = y' (like 'equals' in Java) and reference equality 'x == y' (like '==' in Java).
    Similarly, 'x <> y' is structural inequality and 'x != y' is reference inequality.
  - All variables are immutable. For mutability, use ref cells. Ref cell assignment: 'x := y'; getting the value of a ref cell: '!x'.
    Note: 'x = y', where x and y are ref cells, is equivalent to '!x = !y', i.e. '=' compares the contents instead of the identities of ref cells.

- VeriFast uses OCaml lists extensively. Familiarize yourself with the List module. See library docs at http://caml.inria.fr.
  Additional list manipulation functions are defined in util.ml. Familiarize yourself with them.
  
Mutable state & symbolic execution forks
========================================

VeriFast is written in a partially functional and partially imperative style. In particular,
the symbolic execution state (essentially the heap, the environment, and the path condition) is
partially threaded explicitly in functional style (the heap and the environment) and partially
kept in a mutable data structure (the path condition: it is kept as the state of the SMT solver).
Note: there are also some other pieces of mutable state linked to the symbolic execution state:
- the set of used symbol names (for generating fresh symbol names)
- the symbolic execution trace (for debugging)

Symbolic execution is forked at branching constructs, such as if statements, if assertions,
switch statements, switch assertions, while statements, blocks with gotos, shortcut boolean operators,
and many other places.

It is important that when a branch ends and the next branch is started, the symbolic execution state is
properly reset, i.e. all changes to the path condition, all newly allocated symbol names, etc. are forgotten.
This is done by using the push() and pop() functions, or, more structuredly, the in_temporary_context function.

There are two general strategies for when to push() and pop(): at the time of a change to the mutable state, or
at the time of the start of a branch.

Note: the following are some of the functions that change the mutable state:
- ctxt#assume
- get_unique_var_symb
- ctxt#assume_forall

Since it is impractical to push and pop whenever we call get_unique_var_symb, let us use as the strategy that ***we
push and pop whenever we start a new branch***. Nonetheless, for the sake of "defense in depth", use assume instead
of ctxt#assume etc. whenever it makes sense.

The codebase uses "effect typing" to help check that all branches are "protected" by push and pop. Specifically, each
function that potentially modifies the mutable state should have return type symexec_result, i.e. it should return
SymExecSuccess. To "cast" this type to unit, use function "execute_branch". This function saves and restores the
mutable state.
