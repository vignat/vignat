# The Model Refinement Problem

## Problem Statement

Given: We have a proven correct implementation(I), and a limited-use symbolic model(M) used for symbolic verification of the business logic.

Find: a proof that for all the possible execution paths, the set of model behaviours (B(M)) contain the set of the implementation begaviours(B(I)): B(I) \subset B(M).

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

At the return point of each API function, Klee should remember the symbolic return value and all the modified pointer arguments. ~At the end of the event-loop iteration, it should also be checked, that the starting state is a superset of the finishing state, but that is a different story.~
At the entry point of each API function, Klee gathers the arguments. These info gets attached to the API call in the path-tree. The whole tree is dumped at some point choosen carefully to reduce the overhead but not to miss some path.

## Solution Implementation

### First Step

Dump the sequence of called functions at the end of each analyzed path.
