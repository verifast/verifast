# Expressive modular verification of termination for busy-waiting programs

By Justus Fasse and Bart Jacobs. See also our [paper on arXiv](https://arxiv.org/abs/2312.15379).

This directory contains Java source code for a *cohort lock* implemented on top of a *ticket lock*, itself implemented in terms of atomic machine instructions using busy-waiting. The cohort lock performs *lock handoff*, where a lock is acquired in one thread and released in another, a pattern not supported by classical lock specifications for total correctness.

The source code contains annotations for the [VeriFast](https://github.com/verifast/verifast) program verification tool. Specifically, each `X.javaspec` file contains the specification for the corresponding `X.java` file: `Ticketlock.javaspec` and `CohortLock.javaspec` encode our proposed fair lock specification into VeriFast notation, applied to the ticket lock API and the cohort lock API, respectively. Notice in particular that each method is annotated with `//@ terminates;`, which causes VeriFast to check that the method terminates.

To check that each module satisfies its specification, install the latest VeriFast [nightly build](https://github.com/verifast/verifast/releases/tag/nightly) for your platform and run the following command:

    /path/to/verifast/bin/verifast -c growing_lists.jarsrc ticketlockstrong.jarsrc ticketlock.jarsrc ticketlockclassic.jarsrc classicclient.jarsrc cohortlock.jarsrc spinlock.jarsrc simplehandoffclient.jarsrc busywaitinghandoffclient.jarsrc trickyclient.jarsrc

This should report `0 errors found` for each `.jarsrc` file. (Note: this might print `INFO: Detected an inconsistency after axiom instantiations triggered by the construction of new terms (rather than after adding a new assumption). This might indicate an inconsistency in the axioms` notices. However, this does not actually indicate an inconsistency in the axioms.)

Notes:

- VeriFast performs modular verification. For example, when verifying `CohortLock.java`, it looks only at `Ticketlock.javaspec`, not at `Ticketlock.java`. Since CohortLock and Ticketlock satisfy identical specifications, this means we can conclude that a cohort lock built on top of any other fair lock, including for example another cohort lock, would also be correct.
- In order to further modularize the proof, we implemented class Ticketlock in terms of class TicketlockStrong, whose specification is stronger and simpler than the general fair lock specification we propose in the paper but less abstract: more complex locks such as cohort lock do not satisfy the stronger spec.
- As a sanity check on the fair lock specification, we use it in `ticketlockclassic.jarsrc` to implement a simpler, classical (but less flexible) specification where the module creates and discharges obligations. Furthermore, in `classicclient.jarsrc` we use this classical ticketlock to verify a simple client with a `main` method annotated with `//@ terminates;`, specifying that the closed program as a whole shall terminate.
- We also verified a simple spinlock implementation (in `Spinlock.java`) against our proposed unfair lock spec (in `Spinlock.javaspec`) and verified a number of client programs:
  - `SimpleHandoffClient.java` is the aborting three-thread example from the paper.
  - `BusyWaitingHandoffClient.java` is a version of that example where the middle thread busy-waits for `f` to be cleared instead of aborting.
  - `TrickyClient.java` is an example that was mentioned by TaDA Live's authors [D'Osualdo et al., TOPLAS 2021] as not being supported by TaDA Live.
- In both `SimpleHandoffClient.java` and `BusyWaitingHandoffClient.java`, the left thread burdens the middle thread with new obligations asynchronously, a proof pattern not supported by TaDA Live. We believe TaDA Live does not support the `BusyWaitingHandoffClient.java` example: in the absence of asynchronous burdening, the middle thread must be continuously holding an obligation OM at some level LM, even while busy-waiting for the left thread's obligation OL (at level LL) to clear `f` (so it must be that LL &lt; LM). Let the lock's level be L. Since the right thread's `acquire` operation must wait for OM, we have the constraint LM &lt; L. But the left thread must be holding its obligation OL from the very start, including during its `acquire` operation, so we need L &lt; LL, which is impossible.
- File `_busywaiting.javaspec` declares the axioms that encode our proposed logic for reasoning about termination of busy-waiting.

To play with the proof (and perhaps do some mutation testing), open it in the VeriFast IDE using the following command:

    /path/to/verifast/bin/vfide cohortlock.jarsrc

and click the Play toolbar button to run the verification. (This may take up to 10 seconds in the case of `cohortlock.jarsrc`.)
