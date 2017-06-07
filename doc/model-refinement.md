# The Model Refinement Problem

## Problem Statement

Given: We have a proven correct implementation(I), and a limited-use symbolic
model(M) used for symbolic verification of the business logic.

Find: a proof that for all the possible execution paths, the set of model
behaviours (B(M)) contain the set of the implementation begaviours(B(I)): B(I)
\subset B(M).

## Proposed Solution

1. Modify Klee, so that:
 a. it dumps formulas describing B(M) for each path P - F(Bp(M, P)),
 b. it also dumps the sequence of API calls C(P).
2. Batch together all the F(B(M, P)) for all paths with identical sequence of API calls:
   F(Bc(M, C)) = \union_{P : C(P) = C} F(Bp(M, P))
3. Translate the formulas F(B(M, C)) into an understandable language (e.g. Why3 or CoQ):
   U(F(Bc(M, C)))
4. Express the implementation behaviours in the same language for each call sequence C:
   Bc(I, C)
5. Devise/generate a proof for: \forall C, B(I, C) \subset U(F(Bc(M, C))).

Here, all the steps have to be trusted. So we add to our trusted code base(TCB): 
* Klee modifications: F(Bp(M, P)), C(P),
* Formula batcher: F(Bc(M, C)) and
* Implementation behaviours generator: Bc(I, C).

Each step in more details:

### Klee modifications

At the return point of each API function, Klee should remember the symbolic
return value and all the modified pointer arguments. ~At the end of the
event-loop iteration, it should also be checked, that the starting state is a
superset of the finishing state, but that is a different story.~ At the entry
point of each API function, Klee gathers the arguments. These info gets attached
to the API call in the path-tree. The whole tree is dumped at some point choosen
carefully to reduce the overhead but not to miss some path.

## Solution Implementation

### First Step

Dump the sequence of called functions at the end of each analyzed path. Together
with the arguments and the return values (as well as output-pointers). **done**

*Optional:* write down also the dependencies between the symbolic values,
 collected along the way.

### Second Step

Assemble the common call-path prefixes (matched by the input and output
arguments of the functions called along the way) up to the tip-call of the
prefix. For that generalize the output to compute the complete formula of
possible outcomes. E.g.:

    f(x) -> 3;
    f(x) -> 5; g(z) -> 1; k(34) -> w; and
    f(x) -> 5; g(z) -> 0; k(35) -> l; gives
    
    f(x) -> {3,5}; (tip-call is f(x))
    f(x) -> 5; g(z) -> {0,1}; (tip-call is g(z))
    f(x) -> 5; g(z) -> 1; k(34) -> w; (tip-call is k(34))
    f(x) -> 5; g(z) -> 0; k(35) -> l; (tip-call is k(34))
    

### Third Step

Prove that the complete formula for a tip-function (e.g. {0,1}) covers all the
possible outputs from the model given the call-path prefix.

