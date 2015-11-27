# General Problem Statement

The ultimate goal of the project is to build a network application development framework with the following features:
- strong dependability guarantees
- popularity in the networking community, meaning it should have
  - C/C++ as a development language (may be restricted subset) and
  - competitive performance, and
  - should not require any special knowledge from the verification domain.

We envision the project outcome to consist of the following components:
- support library of verified common-use components, such as
  - verified data structures (hash map, least-prefix-match table, ring)
  - abstraction layer protecting low-level details, like raw pointers.
- language restrictions or extensions, making C/C++ more amenable to automatic reasoning
- (semi)automatic verification tool that leverages the previous components and the domain knowledge to prove certain properties about the user program.

Useful properties to prove:
- crash freedom: there is no such sequence of events, that assuming the trusted code base and hardware is correct would lead the application to crash
- liveness: each packet eventually gets to the processing pipeline
- processing time: the application processes a packet in a predefined number of clocks in any case
- isolation: independent flows can not leak information to each other
- high level specifications refinement: the application behaves according to the user-supplied specifications that describe it in a high level language

We hope that networking domain features alleviate the general verification problem. These features include:
- modularisation with a natural interface: a packet
- limited loops
- limited storage
- prevalence of static allocation
- short execution paths  


# First step: a verified hash-map

Presence of dynamic state creates an enormous input that influences the application behavior, we decided to start with encapsulating it into verified data structures. This allows to reason about unbounded data, and make use of its properties. We started with a hash-map as a popular data structure for network applications.

To simplify the verification, we restricted key and value domains to simple 32bit integer values, and limited the total number of entries by a statically chosen number. We also use a trivial hash-function for the same reason. Our hash table implementation features open addressing scheme, because it involves only arithmetic operations and array indexing. The implementation consists of ~85 lines of C code.

## Approaches Taken
We tried to formally verify that our simple implementation conforms to a set natural properties defining a map. In the search for an optimum, we tried 5 approaches:

**VST**/**Coq**. First approach taken features the least trusted code base (TCB). We used [CompCert](http://compcert.inria.fr/) to translate the C source code into an AST [CoQ](https://coq.inria.fr/) and than applied [VST](http://vst.cs.princeton.edu/) theorems and tactics to prove that it corresponds to the CoQ map implementation. Then we proven that the CoQ map implementation satisfies the required properties. All the proofs are done in CoQ, and machine checkable by its core, which consists of just several thousands lines of trusted code.

The whole process took a long time: a couple of month due to the lack of experience of CoQ interactive theorem prover, poor VST documentation and a substantial effort required to manually proofs all the refinements and handle many details. The complete proof takes more than 3156 lines of CoQ code. It is not a reliable metric, because this code was written by a novice and certainly lacks automation and at the same time contains reusable components, applicable for another similar verification task.

**Dafny**(not finished). To optimize human effort, we decided to try automatic verifiers like [Dafny](http://dafny.codeplex.com/). Dafny has its own memory-safe implementation language and integrated verification constructs such as function contracts and loop invariants. It should be easier and take less code to verify an analogous implementation, although we never finished one. Drawbacks are: 
* dafny-language may be difficult to integrate with client applications written in C
* higher level language may incur performance overhead
* lacks cross-platform support (runs only on windows)
* big trusted code base: Dafny translate the code to [BoogiePL](https://boogie.codeplex.com/) which uses [Z3](https://github.com/Z3Prover/z3/wiki) to check Hoare-triples.

[**Escher C Verifier**](http://www.eschertech.com/products/ecv.php)(not finished) is a commercial tool that does the same job but for superset of a subset of C and C++. It uses special macros to encode verification statements and this way allows developer to compile the verified file with any standard tool. It tries to infere many proof steps automatically, gives a detailed report in the case of failure and sometimes suggests fixes. However it was not enough for us, and the opaqueness and non-intuitiveness of the proof process slowed down the development.

**Frama-C**/**WP**(not finished). [Frama-c](http://frama-c.com/) is an extensible platform for static analysis of C source files. It has several formal verification plugins, one of them - [WP](http://frama-c.com/wp.html)(from Weakest Precondition). It also features a standardized specification language [ACSL](http://frama-c.com/acsl.html), and pluggable theorem provers for the generated verification conditions. Unfortunately, WP does not yet implement ACSL in full, and lacks some necessary features like set-cardinality theory.

[**VeriFast**](http://people.cs.kuleuven.be/~bart.jacobs/verifast/) is another integrated verification system. It works with pure C and uses special comments for verification constructs. It also supports concurrent reasoning from the very beginning. VeriFast uses an old version of Z3 and does uses it only to prove simple elementary statements, aiming predictable performance and leaving the burden of guiding all the proof steps to the developer. This approach involves more manual effort than Dafny, frama-c/WP or eCv, but it is more transparent, and shows the developer to see the exact entailment that is not obvious. The proof took 2300 lines of special-comment annotations that carry out the proof.


# First goal: dependable NAT-box

With the verified map implementation, our next step is to try to plug it into a sample client application and see whether we can make use of its specification to prove some properties of the entire application. We choose a NAT-box for that purpose.

We aim to develop a still useful network address translation(NAT) box that would have some strongly guaranteed properties. We start with crash freedom as the most desired property.

We take [DPDK](http://dpdk.org/) - the perspective platform for network application development - and hope to build our framework on top of it.

## Approach

Given positive past experience with this technology, we start with **symbolic execution**(symbex) approach. It consists of the following parts:
* Transform some loops to simplify execution or finalize the execution paths. In particular:
  * cut the infinite event-processing loop to a single iteration. Use loop invariant to connect subsequent iteration for future induction reasoning
  * replace enumeration of the devices being polled by polling a single symbolic device.
* Prove equivalence for these transformations.
* Provide a symbex-friendly data-structure model that is equivalent to the real one in the usage scenario of the application.
* Prove equivalence of this model an the real data structure specification for the given usage scenario.
* Provide a symbex implementation of the DPDK API, that models all possible input events, in particular it injects a symbolic package to the symbolic device mentioned above.
