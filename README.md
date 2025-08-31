[![CI](https://github.com/verifast/verifast/workflows/CI/badge.svg)](https://github.com/verifast/verifast/actions) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.13620299.svg)](https://doi.org/10.5281/zenodo.13620299)

[[Quick intros](#quick-intros)] [[Proofs done](#proofs-done)] [[Binaries](#binaries)] [[User interfaces](#user-interfaces)] [[Compiling](#compiling)] [[Documentation](#documentation)] [[Getting help](#getting-help)] [[Acknowledgements](#acknowledgements)] [[Mailing lists](#mailing-lists)] [[Third-party resources](#third-party-resources)]

VeriFast
========

By Bart Jacobs\*, Jan Smans\*, and Frank Piessens\*, with contributions by Pieter Agten\*, Cedric Cuypers\*, Lieven Desmet\*, Niels Mommen\*, Jan Tobias Muehlberg\*, Willem Penninckx\*, Pieter Philippaerts\*, Nima Rahimi Foroushaani\*, Amin Timany\*, Thomas Van Eyck\*, Gijs Vanspauwen\*,  Frédéric Vogels\*, and [external contributors](https://github.com/verifast/verifast/graphs/contributors)

\* imec-DistriNet research group, Department of Computer Science, KU Leuven - University of Leuven, Belgium

VeriFast is a research prototype of a tool for modular formal verification of correctness properties of single-threaded and multithreaded C, Rust and Java programs annotated with preconditions and postconditions written in separation logic. To express rich specifications, the programmer can define inductive datatypes, primitive recursive pure functions over these datatypes, and abstract separation logic predicates. To verify these rich specifications, the programmer can write lemma functions, i.e., functions that serve only as proofs that their precondition implies their postcondition. The verifier checks that lemma functions terminate and do not have side-effects. Since neither VeriFast itself nor the underlying SMT solver need to do any significant search, verification time is predictable and low.

The VeriFast source code and binaries are released under the [MIT license](LICENSE.md).

Quick intros
------------

- [A quick introduction to VeriFast for C](intro-c.md)
- [A quick introduction to VeriFast for Rust](intro-rust.md)

Proofs done
-----------

Some of the more notable proofs done with VeriFast (with caveats) include:
- A proof of memory safety and thread safety of [the Linux boot protocol keyboard driver](https://github.com/verifast/verifast/tree/master/examples/usbkbd)
- A proof of absence of array index out of bounds exceptions, null pointer exceptions, and invalid API calls in [(a mock-up of) the Java Card code running on the Belgian electronic identity card](https://github.com/verifast/verifast/tree/master/examples/java/Java%20Card/NewEidCard)
- A modular proof of memory safety, thread safety, and termination of a [cohort lock](https://github.com/verifast/verifast/tree/master/examples/busywaiting/flexiblespecs/ticketlock-java) implemented on top of ticketlocks, themselves implemented using busy waiting, and using lock handoff
- Proofs of integrity and confidentiality of a number of simple [cryptographic protocols](https://github.com/verifast/verifast/tree/master/examples/crypto_ccs) implemented in C using the byte buffer-based APIs of mbed TLS (as opposed to a high-level "symbolic" API).
- A proof of a [floating-point algorithm](https://github.com/verifast/verifast/tree/master/examples/floating_point/sqrt_with_rounding) for computing the square root, taking into account rounding (but not overflow or underflow).
- [Termination of some small Java programs involving dynamic binding](https://github.com/verifast/verifast/tree/master/examples/java/termination) (a.k.a. virtual method calls) and/or concurrency.
- Jayanti's optimal [snapshot algorithm](https://github.com/verifast/verifast/blob/master/examples/jayanti/jayanti.c), using prophecies
- A [concurrent set](https://github.com/verifast/verifast/tree/master/examples/lcset) implemented using lock coupling (a.k.a. hand-over-hand locking).
- A modular proof of a fine-grained concurrent Multiple Compare And Swap ([MCAS](https://github.com/verifast/verifast/tree/master/examples/mcas)) algorithm built on top of a Restricted Double Compare Single Swap algorithm, using helping.
- Termination of various concurrent programs using [monitors](https://github.com/verifast/verifast/tree/master/examples/monitors) and condition variables
- Some small [purely unsafe](https://github.com/verifast/verifast/tree/master/tests/rust/purely_unsafe) (i.e. C-style) Rust programs, including a constant-space tree marking algorithm
- A partial proof of the Rust standard library's [LinkedList](https://github.com/verifast/verifast/tree/master/tests/rust/safe_abstraction/linked_list) and [RawVec](https://github.com/verifast/verifast/tree/master/tests/rust/safe_abstraction/raw_vec) abstractions
- Proofs of simplified versions of Rust's [Cell](https://github.com/verifast/verifast/blob/master/tests/rust/safe_abstraction/cell.rs), [Mutex](https://github.com/verifast/verifast/blob/master/tests/rust/safe_abstraction/mutex.rs), [Rc](https://github.com/verifast/verifast/blob/master/tests/rust/safe_abstraction/rc.rs), [Arc](https://github.com/verifast/verifast/blob/master/tests/rust/safe_abstraction/arc.rs), and [RefCell](https://github.com/verifast/verifast/blob/master/tests/rust/safe_abstraction/ref_cell.rs) abstractions

Binaries
--------

Within an hour after each push to the master branch, binary packages become available [here](https://github.com/verifast/verifast/releases/tag/nightly).

These "nightly" builds are very stable and are recommended. Still, named releases are available [here](https://github.com/verifast/verifast/releases). (An archive of older named releases is [here](https://people.cs.kuleuven.be/~bart.jacobs/verifast/releases/).)

Simply extract the files from the archive to any location in your filesystem. All files in the archive are in a directory named `verifast-COMMIT` where `COMMIT` describes the Git commit. For example, on Linux:

    tar xzf ~/Downloads/verifast-nightly.tar.gz
    cd verifast-<TAB>  # Press Tab to autocomplete
    bin/vfide examples/java/termination/Stack.jarsrc  # Launch the VeriFast IDE with the specified example
    ./test.sh  # Run the test suite (verifies all examples)

**Note (macOS):** To avoid GateKeeper issues, before opening the downloaded archive, remove the `com.apple.quarantine` attribute by running

    sudo xattr -d com.apple.quarantine ~/Downloads/verifast-nightly-osx.tar.gz

The VeriFast MacOS binary is an x86 binary. To run it on Apple Silicon, you need to install Rosetta 2 by running

    softwareupdate --install-rosetta

**Supply chain security:** The CI workflow creates [GitHub Artifact Attestations](https://docs.github.com/en/actions/security-for-github-actions/using-artifact-attestations) for these binaries, so that you can verify that they were generated by a GitHub Actions workflow triggered by a push to this repository. To do so, install the [GitHub CLI](https://cli.github.com) and run

```
gh attestation verify verifast-21.04-352-gbeb57a82-macos.tar.gz --repo verifast/verifast
```
To check for a particular commit SHA, run
```
[ "$(gh attestation verify verifast-21.04-352-gbeb57a82-macos.tar.gz --repo verifast/verifast --format json --jq '.[0].verificationResult.signature.certificate.sourceRepositoryDigest')" = "beb57a820915409f71dbc2a802985e291e60e12d" ]
```

User interfaces
---------------

We offer the following user interfaces:
- The VeriFast IDE (at `bin/vfide` in the distribution)
- The [VeriFast VS Code Extension](https://marketplace.visualstudio.com/items?itemName=VeriFast.verifast)
- The VeriFast command-line tool (at `bin/verifast` in the distribution)

Compiling
---------

- [Windows](README.Windows.md)
- [Linux](README.Linux.md)
- [macOS](README.MacOS.md)

Documentation
-------------

- [The VeriFast Tutorial](https://doi.org/10.5281/zenodo.887906) (for C, but the concepts apply to Rust as well)
- [A tour of the RawVec proof](tests/rust/safe_abstraction/raw_vec/) (Rust)
- [A tour of the LinkedList proof](tests/rust/safe_abstraction/linked_list/) (Rust)
- [Featherweight VeriFast](http://arxiv.org/pdf/1507.07697) [(Slides, handouts, Coq proof)](https://people.cs.kuleuven.be/~bart.jacobs/fvf)
- [Scientific papers](https://people.cs.kuleuven.be/~bart.jacobs/verifast/) on the various underlying ideas
- [VeriFast Docs](https://verifast.github.io/verifast-docs/) (under construction) with a nascent FAQ and a grammar for annotated C/Java source files
- [The VeriFast for Rust Reference](https://verifast.github.io/verifast/rust-reference) (under construction)

Getting help
------------

The maintainer (and, perhaps, other VeriFast users and enthusiasts as well) can be reached for informal chat in the [VeriFast Zulip chatroom](https://verifast.zulipchat.com).

Acknowledgements
----------------

### Dependencies

We gratefully acknowledge the authors and contributors of the following software packages.

#### Bits that we ship in our binary packages

- [OCaml](http://caml.inria.fr)
- [OCaml-Num](https://github.com/ocaml/num)
- [Lablgtk](http://lablgtk.forge.ocamlcore.org)
- [GTK+](https://www.gtk.org) and its dependencies (including GLib, Cairo, Pango, ATK, gdk-pixbuf, gettext, fontconfig, freetype, expat, libpng, zlib, Harfbuzz, and Graphite)
- [GtkSourceView](https://wiki.gnome.org/Projects/GtkSourceView)
- The excellent [Z3](https://github.com/Z3Prover/z3) theorem prover by Leonardo de Moura and Nikolaj Bjorner at Microsoft Research, and co-authors

#### Software used at build time

- findlib, ocamlbuild, camlp4, valac
- Cygwin, Homebrew, Debian, Ubuntu
- The usual infrastructure: GNU/Linux, GNU make, gcc, etc.

### Infrastructure

We gratefully acknowledge the following infrastructure providers.

- GitHub
- The [Zulip](https://zulip.com) team chat app

### Funding

This work is supported in part by the Flemish Research Fund (FWO-Vlaanderen), by the EU FP7 projects SecureChange, STANCE, ADVENT, and VESSEDIA, by Microsoft Research Cambridge as part of the Verified Software Initiative, by the Research Fund KU Leuven, and by the Cybersecurity Research Program Flanders.

Mailing lists
-------------

To be notified whenever commits are pushed to this repository, join the [verifast-commits](https://groups.google.com/forum/#!forum/verifast-commits) Google Groups forum.

Third-Party Resources
---------------------

- Kiwamu Okabe created a [Google Groups forum](https://groups.google.com/forum/#!forum/verifast) on VeriFast
- Kiwamu Okabe translated the VeriFast Tutorial into [Japanese](https://github.com/jverifast-ug/translate/blob/master/Manual/Tutorial/Tutorial.md). Thanks, Kiwamu!
- Joseph Benden created [Ubuntu packages](https://launchpad.net/%7Ejbenden/+archive/ubuntu/verifast)
- Joe Doyle created a VeriFast Users' Group on Matrix at `#vf-users:matrix.org`
