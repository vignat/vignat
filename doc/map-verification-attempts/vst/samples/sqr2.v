Require Import Compare_dec.
Require Import Arith.Mult.
Require Import Arith.Plus.
Require Import Omega.

(** 
  *   Definition of sqrt.
  *)

(** Note: natural numbers in Coq are represented as lists:
  0 = O;  1 = S O;  2 = S (S O);  5 = S (S (S (S (S O)))).
  Infix operators can have a prefix form:
  a <= b <=> le a b;
  a < b <=> lt a b;
  a > b <=> lt a b;
  this operators return truth. They are not computable. 
  A computable analog of 'le' is 'leb'. It returns boolean:
  leb: nat -> nat -> bool.
  It can be used as a condition in an if-statement
*)
  

(** ** auxilary function - emulating iteration with tail recursion.
   guess monotonically decreasing on each call while its square > n 
   function is guaranteed to terminate. (proven automatically due 
   to the form of the function (destructive recursion) 

  Construction "match n with A x y z => ... | B a b c => ... end"
  performs destruction of its argument n by all possible constructors.
  
 *)
Fixpoint guess_sqrt (n guess: nat): nat :=
  match n with 
      | O => O
      | S x => match guess with
                 | O => O
                 | S prv =>
                   if (leb (guess * guess) n) then guess else guess_sqrt n prv
               end
  end.

(** ** wrapper interface function 

  *)
Function sqrt (n: nat) := guess_sqrt n n.

(** 
  *   Testing of the defined function. 

  *)

Eval compute in (sqrt 10).

(** 
                                                                     
  * Correctness proof: $sqrt(n)^2 <= n < (sqrt(n)+1)^2 $
                                                                     
   The main theorem is proven last.                                  

  *)

(** ** A boolean can either be equal to true, or false.
   this lemma helps consider cases in analysis of an if-expression 

  *)
Lemma true_or_false: forall a : bool, a=true \/ a=false.
intro.
induction a.
tauto.
tauto.
Qed.


(** *** guess_sqrt is 0 if the first argument is 0 

  *)
Lemma guess_0_is_0: forall m: nat, guess_sqrt 0 m = 0.
Proof.
induction m.
simpl.
auto.
unfold guess_sqrt.
auto.
Qed.

Lemma guess_le: forall n g:nat, (guess_sqrt n g)*(guess_sqrt n g) <= n.
Proof.
intros.
destruct n.
- rewrite guess_0_is_0.
  auto.
- induction g.
  + unfold guess_sqrt.
    omega.
  + unfold guess_sqrt.
    fold guess_sqrt.
    pose proof true_or_false.
    specialize H with (leb (S g*S g) (S n)).
    decompose sum H.
    * rewrite H0.
      apply leb_complete in H0.
      assumption.
    * rewrite H0.
      apply leb_complete_conv in H0.
      apply IHg.
Qed.

Lemma guess_gt: forall n g: nat, (n < S g * S g) ->
                                 n < (S (guess_sqrt n g))*(S (guess_sqrt n g)).
Proof.
  intros.
  destruct n.
  - rewrite guess_0_is_0.
    auto.
  - induction g.
    auto.
    unfold guess_sqrt; fold guess_sqrt.
    pose proof true_or_false.
    specialize H0 with (leb (S g*S g) (S n)).
    decompose sum H0.
    + rewrite H1.
      assumption.
    + rewrite H1.
      apply leb_complete_conv in H1.
      apply IHg.
      apply H1.
Qed.

(** *** The holy grail: complete correctness proof, combining together two
   parts, proven before. 

  *)
Theorem true_sqrt: forall n :nat, le ((sqrt n)*(sqrt n)) n /\ lt n (S (sqrt n) * S (sqrt n)).
unfold sqrt.
intros.
split.
- apply guess_le.
- apply guess_gt.
  simpl.
  apply le_lt_n_Sm.
  apply le_plus_l.
Qed.

(** *** So far, it is formally proven (modulo Coq core), that:
1) sqrt n terminates for any natural n and 2) x = sqrt n satisfies specification : $(sqrt\ n)^{2} <= n < (1+sqrt\ n)^{2}$
  *)

