# General Problem Statement

The ultimate goal of the project is a network application development framework with the following features:
- strong dependability guarantees
- popularity in the networking community, meaning it should have
  - C/C++ as a development language (or a restricted subset),
  - competitive performance and
  - should not require from the developer any special knowledge from the verification domain.

We envision the project outcome to consist of the following parts:
- support library of verified common-use components, such as
  - verified data structures (hash map, least-prefix-match table, ring)
  - abstraction layer protecting low-level details, like raw pointers for allocated buffers.
- language restrictions or extensions, making C/C++ more amenable to automatic reasoning
- (semi)automatic verification tool that leverages the previous components and the domain knowledge to prove certain properties about the user program.

It is worth to research the actual costomer preference list for those properties. Most likely, it includes:
- *crash freedom*: there is no such sequence of events that, assuming the trusted code base and hardware are correct, would lead the application to crash
- *liveness*: each packet eventually gets to the processing pipeline
- *response time*: the application processes a packet in a predefined number of clocks in any case
- *isolation*: independent flows can not leak information to each other
- *power consumption limit*: the app can not burn more than a given power budget in a time unit
- high level *specifications refinement*: the application behaves according to the user-supplied specifications that describe it in a high level language.

We hope that networking domain features alleviate the general verification complexity. Specifically, the features:
- Modularisation with a natural interface(packet/frame). It decreases the verification problem size that positively affects the exponential-like complexity. It also allows to reuse results between different problems with shared parts.
- Limited loops. Most loops have statically-predictable fixed number of iterations and can be unrolled. Others are still limited in order to keep response time bounded.
- Limited storage. Less variables - less the state-space that we need to reason about.
- Prevalence of static allocation. We do not need to keep complex memory models for dynamic allocation schemes.
- Short execution paths. Therefore amenable to expensive methods, like abstract interpretation.


# First step: a verified hash-map

Dynamic state forms an enormous input that influences the application behavior. We decided to start with encapsulating it into a set of verified data structures following strict specifications. This allows us to reason about unbounded data and make use of its properties. We started with a hash-map as a popular data structure for network applications.

To simplify the verification we restricted key and value domains to simple 32 bit integer values and limited the total number of entries by a statically chosen number. We also use a trivial hash-function. Our hash table implementation features open addressing scheme. It involves only arithmetic operations and array indexing and avoids complex memory shapes. All the mentioned simplifications allowed it to fit into roughly 85 lines of C code with zero dependencies.

## Approaches Taken
We tried to formally verify that our simple implementation conforms to a set natural properties defining a map (see the expiring_map document). In the search for the optimal approach, we tried 5 tool(chain)s:

**VST**/**Coq**. The first approach taken features the least trusted code base (TCB). We used [CompCert](http://compcert.inria.fr/) to translate the C source code into an AST encoded in [CoQ](https://coq.inria.fr/) language and than applied [VST](http://vst.cs.princeton.edu/) theorems and tactics to prove that it corresponds to a CoQ map implementation. Then we proven that the CoQ map implementation satisfies the required properties. All the proofs are done in CoQ and machine checkable by its core, which consists of just several thousands lines of trusted code.

The whole process took a couple of month due to the lack of experience of CoQ interactive theorem prover, poor VST documentation and a substantial effort required to manually prove all the refinements and handle many details. The complete proof comprises 3156 lines of CoQ code. It is not a reliable metric because this code was written by a novice and certainly lacks conciseness and automation and at the same time it counts reusable components, applicable for another similar verification task.

**Dafny**_(not finished)_. To optimize human effort, we decided to try automatic verifiers like [Dafny](http://dafny.codeplex.com/). Dafny by it self is a memory-safe implementation language with integrated verification constructs such as function contracts and loop invariants. It should be easier and take less code to verify an analogous implementation although we never finished one. Drawbacks are: 
* dafny-language may be difficult to integrate with client applications written in C
* higher level language may incur performance overhead
* lack of cross-platform support (runs only on windows)
* big trusted code base: Dafny translate the code to [BoogiePL](https://boogie.codeplex.com/) which uses [Z3](https://github.com/Z3Prover/z3/wiki) to check Hoare-triples.

[**Escher C Verifier**](http://www.eschertech.com/products/ecv.php)_(not finished)_ is a commercial tool that does the same job but for superset of a subset of C and C++. It uses special macros to encode verification statements. This way it allows developer to compile the verified file with any standard tool. It tries to infere many proof steps automatically, gives a detailed report in the case of failure and sometimes suggests fixes to specifications. All this was not enough for our task, and the opaqueness and non-intuitiveness of the proof process slowed down the development.

**Frama-C**/**WP**_(not finished)_. [Frama-c](http://frama-c.com/) is an extensible platform for static analysis of C source files. It has several formal verification plugins, one of them is [WP](http://frama-c.com/wp.html)(from the [Weakest Precondition][1]). It also features a standardized specification language [ACSL](http://frama-c.com/acsl.html) and pluggable theorem provers for the generated verification conditions. Unfortunately, WP does not yet implement ACSL in full and lacks some necessary features like set-cardinality theory.

[**VeriFast**](http://people.cs.kuleuven.be/~bart.jacobs/verifast/) is another integrated verification system. It works with pure C and uses special comments for verification constructs. It also supports concurrent reasoning from the very beginning. VeriFast uses an old version of Z3 and uses it only to prove simple elementary statements, aiming predictable performance and expecting the developer to put all the proof steps. This approach involves more manual effort than Dafny, frama-c/WP or eCv, but it is more transparent and shows the developer the exact implication that was not obvious to a solver. The entire proof took 2300 lines of special-comment annotations that carry out the proof, and that include some relatively general reusable theories developed on the way.


# First goal: dependable NAT-box

With the verified map implementation, our next step is to plug it into a sample client application and see whether we can make use of its specification to prove some properties of the entire application. We choose a network address translation uint (NAT-box) for that purpose. It uses a hash table to store active flows.

We aim to develop a yet useful NAT-box that would have some strongly guaranteed properties. We start with crash freedom as probably the most desired property.

We take [DPDK](http://dpdk.org/) - a promising platform for high-performance network application development - and hope to build our framework on top of it.

## Approach

We start with **symbolic execution**(symbex) technology, given some positive past experience. Our approach consists of the following parts:
* Transform some loops to simplify execution or finalize the execution paths. In particular:
  * cut the infinite event-processing loop to a single iteration. Use loop invariant to connect subsequent iteration for future induction reasoning
  * replace enumeration of the devices being polled by polling a single symbolic device.
* Prove equivalence for these transformations.
* Provide a symbex-friendly data-structure model that is equivalent to the real one in the usage scenario of the application.
* Prove equivalence of this model an the real data structure specification for the given usage scenario.
* Provide a symbex implementation of the DPDK API, that models all possible input events, e.g. it injects a symbolic package to the symbolic device receive queue.
* Instrument the application code with bounds checks to assure memory safety during the symbex.

The symbolic model starts in a state that generalizes all possible states of the formal data structure, exectes transforming the state the same way the data structure would transform and therefore it ends up in a state that generalizes a subset of possible data structure states closing the loop. We do not need to synchronize the symbolic state with the possible states of the real implementation, because correctness of each function ensures it. Regarding additional control functions:
* read-only functions should not do any harm
* write functions need more thought. IMO, they can be invoked only from a higher-level model, and should represent the alterations made by it to the lower-level model in the modeled code. In other words, this "control" functions are to be called from a symbolic model of the function to represent and generalize a sequence of normal calls to the lower-level model.

## Challenges

The key design trade off in the problem is simplicity <-> dependability. We aim to provide stronger guarantees for the applications developed in the framework, but we also do not want to submerse the networking developer with verification effort. Apart from the key design challenge, we have met some technical ones inherent to the methodology chosen (some of the tool-specific issues are described above):

* Symbolic index (see below)
* Unstable memory layout and other environment properties that are difficult to model. C language makes it difficult to completely isolate the programm from the runtime environment. This includes also a time-dependent control flow. However, strict standard compliance may aleviate the memory layout dependence (expressed in pointer arithmetic/comparisons), should be easy to enforce statically, but may be hard to eradicate.
* Models refinement. As indicated in the approach section, we use two different models of a map data structure:
  * formally verified usable implementation and
  * symbolic image, capable of handling a limited number of usage scenarios
  
  as well as two programs:
  * the original one with an infinite event-handling loop and
  * the modified one, with bounded control flow paths.
  
  For these models we need to prove the refinement property, i.e. that one is equivalent to another under reasonable conditions.
* Tracking time. The NAT expires flows over time. Time concept requires special attention, and should be explicitly passed as an argument for API calls.
* Need for a formal model of DPDK. DPDK has pretty scarce documentation and is under active development, so the ad-hoc model replacing the real low-level code also requires validation.
* Generalization. How do we generalize the specific NAT case to an abstract network dataplane application.

## Current implementation simplifications

The partially-verified NAT-box aims to a single-threaded multiple-internal/single-external port dynamic polling mode network address translation unit that uses port number as a flow identifier. However in its present state it lacks the following features to be considered a practical implementation:
* Flow expiration. Currently once added flow lives forewer leading to the flowtable overflow.
* Available ports pool. In the present implementation for a new flow a new port always allocated. It is totally adequate the zero-deallocation policy, but when we fix the flow expiration bullet, the ports will become a scarce resource, and we will need a list data structure (which should not be difficult to verify, though), or something more efficient. For the more efficient appropriate datastructure one can consult the verified garbage collectors works.
* The same goes with the memory for stored flow-entries.
* Performance. The map, as well as the nat-box itself, is not optimized for performance, so it need some optimizations to keep up with the user expectations. Concurrency would be a nice thing to support, given that DPDK has it enabled by design. Benchmark is to be done.
* L2 routing. The current implementation operates on L3, and does not implement ARP and uses a broad cast Ethernet address instead. Therefore receiving NICs usually drop such packets. As Ethernet configuration changes rarely, one possibility is to use a static preconfigured lookup table.

## The list of unsolved problems

* Simplifications. While the NAT implementation bears the aforementioned simplifications, it is not usable.
* Refinement between the symbolic map model and the proven map model.
* Refinement between the symbolic DPDK model and the real DPDK behaviour.
* Formalisation and justification of the required code transformations.
* As mentioned above the implementation currently does not use the verified map. One obstacle here is that the keys in that map are pinned to be 32-bit integers, and that is not enough to uniqly identify a flow. We need to generalize the verified map at least for greater keys.
* The current verified map search is 'O(n)' for the abscent elements, which shoud be a common case for a NAT. A simple optimization could greatly reduce that search time, but it will require a reverification, because it changes the insertion, search and erase code and complicates the internal representation.

# Possible methods
Here we discuss verification methods that could potentially solve our problem.

## Code generation

Systems verified:
 - seL4(micro kernel):
  * certified logical implementation
  * extracted Haskell code
  * hand-writtern optimized C-code 
 -  FSCQ(file system)
  * certified Gallina implementation
  * extracted Haskell code
  * low-level driver

Unfortunately, it seems to be applicable only to the whole-system design. At least it relies on a high-level language like Gallina(in CoQ), or Isabelle logic language.

## Typed assembly language(TAL) with asserts

Systems verified:
 - Verve (OS); ironclad apps; ironfleet
  * TAL checker
  * Boogie
  * Dafny

Again uses high-level languages.

## Symbolic verification + provided certified components

### The symbolic index problem.

Consider the wollowing extract:

```C
int arr[100];
initialize(arr);
int i = symbolic_int();
assume(0 <= i && i < 100);
arr[i] = arr[i] + 1;
check(arr);
```

Depending on the symbex engine and contents of the `check` function, the execution may fork in different ways:
* (most likely) if the condition `check` is complex or the symbex engine follows the naive approach, it will fork 100 execution paths for all possible values of `i`
* if the condition `check` does not depend on the values stored in `arr`, `arr` is not used later on, and the symbex engine is lazy, it will ignore this part
* if the condition `check` is simple enough, e.g.:

  ```C
  void initialize(int* arr) { for (int i = 0; i < 100; ++i) arr[i] = 0; }
  void check(int* arr) {
      assert(arr[1] > arr[0]);
  }
  // no further references of arr.
  ```

  and the symbex engine has this specific optimization, it may fork just three execution paths: 
  * `i == 0` (such that `arr[0]` is incremented),
  * `i == 1` (such that `arr[1]` is incremented) and
  * `i > 1` (that does not affect the `check` condition).
* and finally, if the symbex engine supports array(map) theory, in some cases it may conclude that the `arr[i]++` transformation does not change the `check` condition and avoid the fork completely. E.g.:

  ```C
  void initialize(int* arr) { for (int i = 0; i < 100; ++i) arr[i] = 0; }
  void check(int* arr) {
      for (int i = 0; i < 100; i += 2) assert(arr[i] >= 0);
  }
  // no further references of arr
  ```

  however it requires quite sophisticated analysis, which may be expensive on its own.

The later two cases also require to ensure first, that the `arr` can not be referenced by some "unrelated" pointer later on. The problem becomes disasterous with unbound symbolic pointers. Possible ways to tackle the path explosion:
* modify code to circumvent such cases
* add array(map) theory support to the engine, and profile the symbolic execution to make sure it can gracefully handle symbolic dereference as described above
* wrap such code into separately verified datastructures and teach the engine work with the abstract specifications rather than raw memory layouts. 

## Manual formal verification

E.g. with VST

- Requires substential expertise from the developer.
- Requires much a lot of human effort.

## Automated formal verification

E.g. with VeriFast.

- Again requires expertise from the developer. (However, might be amenable to some heuristics)
- Bigger TCB

[1]: https://en.wikipedia.org/wiki/Predicate_transformer_semantics#Specification_statement_.28or_weakest-precondition_of_procedure_call.29
