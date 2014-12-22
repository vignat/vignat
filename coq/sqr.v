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

(** ** The first part of the correctness proof.
   $guess\_sqrt^{2} <= n $

  *)
Lemma guess_no_more: forall n m :nat, le ((guess_sqrt n m)*(guess_sqrt n m)) n.
Proof.
induction m.
destruct n.
unfold guess_sqrt.
compute; apply Le.le_0_n.
unfold guess_sqrt.
compute; apply Le.le_0_n.
destruct n.
unfold guess_sqrt.
compute; apply Le.le_0_n.
unfold guess_sqrt.
fold guess_sqrt.
cut ((leb (S m * S m) (S n) = true) \/ (leb (S m * S m) (S n)) = false).
intro.
elim H; clear H; intro.
rewrite H.
apply leb_complete.
assumption.
rewrite H.
assumption.
apply true_or_false.
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

(** *** guess_sqrt is 0 if the second argument is 0 

  *)
Lemma guess_n_0_is_0: forall n: nat, guess_sqrt n 0 = 0.
Proof.
destruct n.
auto.
auto.
Qed.

(** *** after a point x, such that n < (x+1)*(x+1), guess_sqrt is a flat constant. 

  *)
Lemma guess_saturation: forall n r: nat, lt n (S r * S r) -> guess_sqrt n r = guess_sqrt n (S r).
Proof.
destruct n.
intros.
repeat rewrite guess_0_is_0.
auto.
intros.
unfold guess_sqrt.
fold guess_sqrt.
apply leb_correct_conv in H.
rewrite H.
auto.
Qed.

(** *** untill a very last point x, such that x*x < n, guess_sqrt is an
   identity function on its second argument 

  *)
Lemma guess_identity: forall n r: nat, le (r * r) n -> guess_sqrt n r = r.
Proof.
intros.
destruct n.
apply Le.le_n_0_eq in H.
symmetry in H.
apply mult_is_O in H.
decompose sum H;rewrite H0;apply guess_0_is_0.
destruct r.
apply guess_n_0_is_0.
unfold guess_sqrt. fold guess_sqrt.
apply leb_correct in H.
rewrite H.
auto.
Qed.

(** *** guess_sqrt reach a saturation on a certain level r, which satisfy
   n < (r + 1)*(r + 1) 

  *)
Lemma guess_saturation_level: forall n r d: nat, lt n (S r * S r) ->
                                                 guess_sqrt n r = r ->
                                                 guess_sqrt n (r + d) = r.
Proof.
intros.
induction d.
rewrite Plus.plus_0_r.
assumption.
rewrite <- plus_n_Sm.
pose proof guess_saturation as I.
specialize I with (n:=n) (r:=(r+d)).
rewrite <- IHd at 2.
symmetry.
apply I.
apply Lt.lt_le_trans with (n:=n) (m:=S r * S r) (p:=S (r + d) * S (r + d)).
assumption.
apply mult_le_compat;omega.
Qed.

(** *** auxilary lemma about decomposition a natural number into two summands

  *)
Lemma nat_decompose: forall n m: nat, le n m -> exists x: nat, n + x = m.
Proof.
intros.
exists (m - n).
omega.
Qed.

(** *** guess saturates at a level r ( if it exists, such that n < (r + 1)*(r + 1) ),
  and returns the same value for any number m >= r 

  *)
Lemma guess_sat_lvl: forall n r m: nat, le r m -> lt n (S r * S r) ->
                                        guess_sqrt n r = r ->
                                        guess_sqrt n m = r.
Proof.
intros.
apply nat_decompose in H.
decompose record H.
rewrite <- H2.
apply guess_saturation_level.
assumption.
assumption.
Qed.

(** *** A square root approximation r exists for any natural number, and satisfies
  the following condition: r*r <= n < (r+1)*(r+1) 

  *)
Lemma sqrt_exists: forall n: nat, exists r: nat, le (r*r) n /\ lt n (S r * S r).
Proof.
induction n.
exists 0.
auto.
decompose record IHn.
cut (S x * S x <= S n \/ S n < S x * S x).
intro ALT.
decompose sum ALT.
- exists (S x).
         split.
         assumption.
         rewrite mult_succ_l.
         rewrite mult_succ_r.
         rewrite <- plus_n_Sm.
         apply lt_n_S.
         rewrite H1.
         rewrite plus_n_O at 1.
         rewrite <- plus_assoc.
         apply plus_lt_compat_l.
         omega.
- exists x.
         split.
         auto.
         assumption.
- apply le_or_lt.
Qed.

(** *** The second part of the correctness proof.
   $n < (guess_sqrt + 1)^{2} $

  *)
Lemma guess_no_less: forall n m: nat, m >= n -> lt n (S (guess_sqrt n m) * S (guess_sqrt n m)).
Proof.
intros.
pose proof sqrt_exists as E.
specialize E with n.
decompose record E.
assert (le x m).
apply le_trans with (n:=x) (m:=n) (p:=m).
- destruct x.
  auto.
  simpl in H1.
  apply lt_le_S.
  apply le_lt_n_Sm in H1.
  apply lt_S_n in H1.
  apply Lt.le_lt_trans with (n:= x) (m:= x + x * S x) (p:=n).
  apply le_plus_trans.
  auto.
  assumption.
- auto.
- rewrite guess_sat_lvl with (n:=n) (r:=x) (m:=m).
  omega.
  assumption.
  assumption.
  apply guess_identity.
  auto.
Qed.

(** *** The holy grail: complete correctness proof, combining together two
   parts, proven before. 

  *)
Theorem true_sqrt: forall n :nat, le ((sqrt n)*(sqrt n)) n /\ lt n (S (sqrt n) * S (sqrt n)).
unfold sqrt.
intros.
split.
apply guess_no_more.
apply guess_no_less.
auto.
Qed.

(** *** So far, it is formally proven (modulo Coq core), that:
1) sqrt n terminates for any natural n and 2) x = sqrt n satisfies specification : $(sqrt\ n)^{2} <= n < (1+sqrt\ n)^{2}$
  *)

