Require Import floyd.proofauto.
Require Import sqrt.
Require Import sqr.
Require Import ZArith.Znat.
Local Open Scope logic.
Local Open Scope Z.

Inductive repr : Z -> val -> Prop :=
| mk_repr : forall z, z >= 0 -> z < Int.modulus -> repr z (Vint (Int.repr z)).

Lemma repr0_is_0 z n:
  repr z (Vint n) -> Int.eq n (Int.repr 0) = true -> z = 0.
Proof.
inversion 1. subst. intro A.
symmetry in A. apply binop_lemmas.int_eq_true in A.
rewrite A in H. inv H.
rewrite Int.Z_mod_modulus_eq.
SearchAbout "mod".
symmetry.
apply Zmod_small.
split.
omega.
assumption.
Qed.

Lemma repr_eq0_not0 z :
  Int.eq (Int.repr z) (Int.repr 0) = false -> z <> 0.
Proof.
intros H; generalize (Int.eq_spec (Int.repr z) (Int.repr 0)); rewrite H.
intros H2 H3; rewrite H3 in H2; apply H2; auto.
Qed.


Lemma repr0_sq_is0 z n:
  repr z (Vint n) -> Int.eq n (Int.repr 0) = true -> z = z*z.
Proof.
intros H A.
apply repr0_is_0 with (z:=z) (n:=n) in A.
subst z.
auto.
assumption.
Qed.

Print Z.
Print positive.

Local Open Scope Z_scope.
Check Z.of_nat.
Check Z.to_nat.

Definition guess_sqrtZ(n guess: Z): Z :=
  Z.of_nat (guess_sqrt (Z.to_nat n)
                       (Z.to_nat guess)).
  
Definition sqrtZ(n : Z): Z :=
  Z.of_nat (sqrt (Z.to_nat n)).
  


Definition guess_sqrt_spec :=
 DECLARE _guess_sqrt
  WITH sh : share, n : Z, guess : Z, vn : val, vguess : val 
  PRE [_n OF tuint, _guess OF tuint ]
      PROP(repr n vn ; repr guess vguess ; 0 <= n < Int.modulus;
          0 <= guess ; guess*guess < Int.modulus)
      LOCAL (`(eq vn) (eval_id _n); `(eq vguess) (eval_id _guess))
      SEP ()
  POST [ tuint ] local (`(eq (Vint (Int.repr (guess_sqrtZ n guess)))) retval).

Definition sqrt_spec :=
 DECLARE _sqrt
  WITH sh: share, n: Z, vn : val
  PRE [_n OF tuint] PROP(repr n vn /\ 0 <= n /\ n*n < Int.modulus)
          LOCAL(`(eq vn) (eval_id _n)) SEP ()
  POST [ tuint ] local (`(eq (Vint (Int.repr (sqrtZ n)))) retval).

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := guess_sqrt_spec :: sqrt_spec :: nil.

Lemma guessZ0_is_0: forall g, guess_sqrtZ 0 g = 0.
Proof.
intros.
unfold guess_sqrtZ.
rewrite <- Nat2Z.inj_0 at 2.
apply Nat2Z.inj_iff.
unfold Z.to_nat at 1.
apply guess_0_is_0.
Qed.

Lemma guessZn0_is_0: forall n, guess_sqrtZ n 0 = 0.
Proof.
  intros.
  unfold guess_sqrtZ.
  rewrite <- Nat2Z.inj_0 at 2.
  apply Nat2Z.inj_iff.
  unfold Z.to_nat at 2.
  apply guess_n_0_is_0.
Qed.

Lemma x_less_sq_x: forall x: Z, 0 <= x -> x <= x*x.
Proof.
intros.
pose (n := Z.to_nat x).
assert (x = Z.of_nat n).
symmetry.
apply Z2Nat.id.
assumption.
rewrite H0.
apply Z2Nat.inj_le.
omega.
rewrite <- H0.
SearchPattern (0 <= _*_).
apply Fcore_Zaux.Zsame_sign_imp.
omega.
omega.
rewrite Nat2Z.id.
SearchAbout Z.to_nat.
rewrite Z2Nat.inj_mul.
rewrite Nat2Z.id.
Search le.
SearchAbout mult.
destruct n.
auto.
simpl.
SearchAbout plus.
rewrite <- plus_Sn_m.
Search le.
SearchAbout plus.
rewrite plus_n_O at 1.
apply plus_le_compat_l.
Search le.
apply le_0_n.
omega.
omega.
Qed.

Lemma g_sq_less_n: forall n guess, 0 <= n < Int.modulus -> 0 <= guess ->
                                   guess*guess < Int.modulus ->
                                   negb (Int.ltu (Int.repr n)
                                                 (Int.mul (Int.repr guess)
                                                          (Int.repr guess))) = true ->
                                   guess*guess <= n.
Proof.
intros n guess Nlim G0 GM H.
apply negb_true_iff in H.
apply ltu_repr_false in H.
unfold Int.unsigned in H.
simpl in H.
assert (guess = Int.Z_mod_modulus guess).
rewrite Int.Z_mod_modulus_eq.
SearchAbout "mod".
symmetry.
apply Zmod_small.
split.
assumption.
pose proof x_less_sq_x as SQ.
specialize SQ with guess.
omega.
rewrite <- H0 in H.
omega.
unfold Int.max_unsigned.
omega.
unfold Int.unsigned.
unfold Int.max_unsigned.
simpl.
split.
rewrite Int.Z_mod_modulus_eq.
rewrite Zmod_small.
SearchPattern (0 <= _ * _).
apply Fcore_Zaux.Zsame_sign_imp.
omega.
omega.
split.
assumption.
pose proof x_less_sq_x as SQ.
specialize SQ with guess.
omega.
rewrite Int.Z_mod_modulus_eq.
rewrite Zmod_small.
assert (guess*guess <= Int.modulus - 1) as GGM by omega.
unfold Int.modulus in GGM.
simpl in GGM.
auto.
split.
assumption.
pose proof x_less_sq_x as SQ.
specialize SQ with guess.
omega.
Qed.

Lemma le_sq_0: forall x:Z, 0 <= x -> 0 <= x*x.
Proof.
intros.
assert (A := x_less_sq_x x H).
omega.
Qed.

Lemma guessZ_saturation: forall n g: Z, 0 < g -> 0 <= n ->
                                        g*g > n -> guess_sqrtZ n g = guess_sqrtZ n (g-1).
Proof.
intros.
unfold guess_sqrtZ.
pose (nn := Z.to_nat n).
pose (ng := Z.to_nat g).
assert (n = Z.of_nat nn) by ( unfold nn; rewrite Z2Nat.id; auto).
assert (g = Z.of_nat ng) by ( unfold ng; rewrite Z2Nat.id; omega).
rewrite H2 in H1.
rewrite H3 in H1.
rewrite <- Nat2Z.inj_mul in H1.
rewrite <- Nat2Z.inj_gt in H1.
red in H1.
assert (ng > 0)%nat.
omega.
pose (pg := pred ng).
assert (ng = S pg).
unfold pg.
symmetry.
apply NPeano.Nat.lt_succ_pred with 0%nat.
unfold ng.
rewrite Nat2Z.inj_lt.
simpl. rewrite Z2Nat.id; omega. 
rewrite H5 in H1.
apply guess_saturation in H1.
assert (pg = Z.to_nat (g - 1)).
unfold pg.
rewrite pred_of_minus.
unfold ng.
rewrite Z2Nat.inj_sub.
simpl.
congruence.
omega.
unfold nn in H1.
rewrite <- H5 in H1.
rewrite H6 in H1.
unfold ng in H1.
rewrite H1.
congruence.
Qed.

Lemma body_guess: semax_body Vprog Gprog f_guess_sqrt guess_sqrt_spec.
Proof.
  start_function.
  destruct H1 as [A0 AM].
  rename H2 into B0, H3 into BM.
  name narg _n.
  name guessarg _guess.
  forward_if (PROP (repr n vn /\ n > 0)
                   LOCAL (`(eq vn) (eval_id _n); `(eq vguess) (eval_id _guess)) SEP ()).
  - forward.
    apply repr0_is_0 in H; [|assumption].
    rewrite H.
    rewrite guessZ0_is_0.
    entailer.
  - forward. entailer. inv H. assert (n <> 0) by ( apply repr_eq0_not0; assumption ).
    entailer.
  - forward_if (PROP (repr guess vguess /\ guess > 0)
                     LOCAL (`(eq vguess) (eval_id _guess);
                            `(eq vn) (eval_id _n)) SEP()).
    + forward.
      apply repr0_is_0 in H0; [|assumption].
      rewrite H0.
      rewrite guessZn0_is_0.
      entailer.
    + forward. entailer. inv H0. assert (guess <> 0) by ( apply repr_eq0_not0; assumption).
      entailer.
    + forward_if (PROP (repr guess vguess /\ guess > 0;
                       guess*guess > n)
                       LOCAL(`(eq vguess) (eval_id _guess);
                             `(eq vn) (eval_id _n)) SEP()).
      * forward.
        inv H0.
        inv H.
        apply g_sq_less_n in H2.
        unfold guess_sqrtZ.
        rewrite guess_identity.
        rewrite Z2Nat.id.
        entailer.
        assumption.
        rewrite <- Z2Nat.inj_mul.
        apply Z2Nat.inj_le.
        apply Fcore_Zaux.Zsame_sign_imp; omega.
        assumption.
        assumption.
        assumption.
        assumption.
        split; assumption.
        assumption.
        assumption.
      * forward. entailer!.
        apply negb_false_iff in H2.
        inv H.
        inv H0.
        SearchAbout Int.mul.
        rewrite mul_repr in H2.
        apply ltu_repr in H2.
        omega.
        split; [omega|unfold Int.max_unsigned;omega].
        split.
        apply le_sq_0; omega.
        unfold Int.max_unsigned; omega.
      *  forward_call (sh,n,guess-1,vn,Vint (Int.sub (Int.repr guess) (Int.repr 1))).
         entailer!.
         subst vn.
         assumption.
         inv H0. constructor. omega.
         omega.
         cut ((guess - 1)*(guess - 1) <= guess*guess).
         omega.
         apply Zmult_le_compat; omega.
         inv H0. inv H9. unfold Int.sub.
         assert (guess - 1 = Int.unsigned (Int.repr guess) - Int.unsigned (Int.repr 1)).
         unfold Int.unsigned. unfold Int.intval. unfold Int.repr. 
         rewrite Int.Z_mod_modulus_eq.
         rewrite Int.Z_mod_modulus_eq.
         rewrite Zmod_small.
         rewrite Zmod_small;omega.
         omega.
         rewrite H0. congruence.
         after_call; forward.
         apply guessZ_saturation in H2.
         rewrite H2.
         congruence.
         omega.
         assumption.
Qed.

Lemma body_sqrt: semax_body Vprog Gprog f_sqrt sqrt_spec.
Proof.
  start_function.
  destruct H as [HR HL].
  destruct HL as [Hm HM].
  name narg _n.
  forward_call (sh,n,n,vn,vn).
  entailer!.
  rewrite <- H0; assumption.
  rewrite <- H0; assumption.
  split.
  omega.
  apply x_less_sq_x in Hm.
  omega.
  after_call.
  forward.
Qed.

Existing Instance NullExtension.Espec.

Theorem all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_skipn.
semax_func_cons body_guess.
semax_func_cons body_sqrt.
apply semax_func_nil.
Qed.

