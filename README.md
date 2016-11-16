[![Build Status](https://travis-ci.org/verifast/verifast.svg?branch=master)](https://travis-ci.org/verifast/verifast) [![Build status](https://ci.appveyor.com/api/projects/status/1w7vchky3k6erltw?svg=true)](https://ci.appveyor.com/project/verifast/verifast)

VeriFast
========

By Bart Jacobs\*, Jan Smans\*, and Frank Piessens\*, with contributions by Pieter Agten\*, Cedric Cuypers\*, Lieven Desmet\*, Jan Tobias Muehlberg\*, Willem Penninckx\*, Jörg Pfähler\*\*\*, Pieter Philippaerts\*, Amin Timany\*, Thomas Van Eyck\*, Gijs Vanspauwen\*,  Frédéric Vogels\*, and Arseniy Zaostrovnykh\*\*

\* imec-DistriNet research group, Department of Computer Science, KU Leuven - University of Leuven, Belgium  
\*\* Institute of Computer and Communication Sciences, École Polytechnique Fédérale de Lausanne  
\*\*\* Institute for Software & Systems Engineering, University of Augsburg

VeriFast is a research prototype of a tool for modular formal verification of correctness properties of single-threaded and multithreaded C and Java programs annotated with preconditions and postconditions written in separation logic. To express rich specifications, the programmer can define inductive datatypes, primitive recursive pure functions over these datatypes, and abstract separation logic predicates. To verify these rich specifications, the programmer can write lemma functions, i.e., functions that serve only as proofs that their precondition implies their postcondition. The verifier checks that lemma functions terminate and do not have side-effects. Since neither VeriFast itself nor the underlying SMT solver need to do any significant search, verification time is predictable and low.

The VeriFast source code and binaries are released under the [MIT license](LICENSE.md).

Binary releases
---------------

For now, see [here](http://distrinet.cs.kuleuven.be/software/VeriFast/) for binary releases.

Compiling
---------
- [Windows](README.Windows.md)
- [Linux](README.Linux.md)
- [Mac OS X](README.MacOS.md)

Documentation
-------------

- [The VeriFast Tutorial](https://people.cs.kuleuven.be/~bart.jacobs/verifast/tutorial.pdf)
- [Featherweight VeriFast](http://arxiv.org/pdf/1507.07697) [(Slides, handouts, Coq proof)](https://people.cs.kuleuven.be/~bart.jacobs/fvf)
- [Scientific papers](https://people.cs.kuleuven.be/~bart.jacobs/verifast/) on the various underlying ideas

Acknowledgements
----------------

This work is supported in part by the Flemish Research Fund (FWO-Vlaanderen), by the EU FP7 projects SecureChange, STANCE, and ADVENT, by Microsoft Research Cambridge as part of the Verified Software Initiative, and by the Research Fund KU Leuven.

Third-Party Resources
---------------------

- Kiwamu Okabe created a [Google Groups forum](https://groups.google.com/forum/#!forum/verifast) on VeriFast
- Kiwamu Okabe translated the VeriFast Tutorial into [Japanese](https://github.com/jverifast-ug/translate/blob/master/Manual/Tutorial/Tutorial.md). Thanks, Kiwamu!
