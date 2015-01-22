Require Import Coq.ZArith.Zbool.
Require Import Coq.ZArith.BinInt.
Require Import ZArith.ZArith_dec.
Require Import ZArith.ZArith_base.
Require Import ZArith.Zdiv.
Require Import Coq.Setoids.Setoid.
Require Import Classical.
Require Import Psatz.

Local Open Scope Z.

Record ClosureMapZ := mk_map {
                   contents: Z->option Z;
                   size: Z
                 }.

Function mGet (m : ClosureMapZ) (k : Z) : option Z :=
  (contents m) k.


Function mPut (m : ClosureMapZ) (k : Z) (v : Z) : ClosureMapZ := 
  {| contents := (fun (x:Z) => if (Z.eq_dec x k)
                               then Some v
                               else (contents m) x);
     size := (match mGet m k with
                | Some _ => (size m)
                | None => (size m) + 1
              end) |}.

Lemma mGetPut1: forall m k v, mGet (mPut m k v) k = Some v.
Proof.
  intros.
  unfold mGet, mPut.
  simpl.
  destruct Z.eq_dec;tauto.  
Qed.

Lemma mGetPut2: forall m k1 k2 v, k1 <> k2 -> mGet (mPut m k1 v) k2 = mGet m k2.
Proof.
  intros.
  unfold mGet, mPut.
  simpl.
  destruct Z.eq_dec;[rewrite e in H|];tauto.
Qed.

Lemma mPutOld: forall m k v, mGet m k = None -> size (mPut m k v) = size m + 1.
Proof.
  intros.
  unfold mPut.
  simpl.
  rewrite H.
  tauto.
Qed.

Lemma mPutNew: forall m k v x, mGet m k = Some x -> size (mPut m k v) = size m.
Proof.
  intros.
  unfold mPut.
  simpl.
  rewrite H.
  tauto.
Qed.

Function loop (k:Z): Z :=
  Z.rem ((Z.rem k 100) + 100) 100.

Definition Bound := 100.

Record ArrMapZ := mk_lmap {
                      values : Z->Z;
                      keys : Z->Z;
                      busybits : Z->bool
                    }.

(* search goes from index + 100 down with round up from 0,
 so i runs from 99 down to 0. first checked cell are
 start + 100 = start. then
 start + 99 = start - 1 mod 100
 etc.*)

Function find_empty (m : ArrMapZ) (start : Z) (i : nat): option Z :=
  if (busybits m (loop (1 + start + Z.of_nat i)))
  then match i with
         | S p => find_empty m start p
         | O => None
       end
  else Some (loop (1 + start + Z.of_nat i)).

Function find_key (m : ArrMapZ) (start : Z) (key : Z) (i : nat): option Z :=
  if (andb (busybits m (loop (1 + start + Z.of_nat i)))
           (Z.eqb key (keys m (loop (1 + start + Z.of_nat i)))))
  then Some (loop (1 + start + Z.of_nat i))
  else match i with
         | S p => find_key m start key p
         | O => None
       end.

Function amGet (map : ArrMapZ) (key : Z) : option Z :=
  match find_key map (loop key) key 99 with
    |Some index => Some (values map index)
    |None => None
  end.

Function amPut (map : ArrMapZ) (key : Z) (val : Z) : option ArrMapZ :=
  match find_empty map (loop key) 99 with
    |Some index => Some {|values:= (fun (i:Z) =>
                                      if (Z.eq_dec i index)
                                      then val
                                      else values map i);
                          keys:= (fun (i:Z) =>
                                    if (Z.eq_dec i index)
                                    then key
                                    else keys map i);
                          busybits:= (fun (i:Z) =>
                                        if (Z.eq_dec i index)
                                        then true
                                        else busybits map i) |}
    |None => None
  end.

(*
Definition full (m : ArrMapZ) :=
  forall i, 0 <= i < 100 -> is_true (busybits m i).
*)

Definition full (m : ArrMapZ):Prop :=
  forall k, is_true (busybits m (loop k)).

Lemma not_forall_exists: forall A, forall P:A->Prop,
                           ~ (forall x:A, P x) -> exists x:A, ~ P x.
Proof.
  intros.
  apply Peirce.
  intro.
  exfalso.
  apply H.
  intro.
  apply Peirce.
  intro.
  exfalso.
  apply H0.
  exists x.
  unfold "~".
  apply H1.
Qed.

Lemma loop_100: forall k, loop (k + 100) = loop k.
Proof.
  intros.
  unfold loop.
  destruct k;simpl.
  - auto.
  - replace (Z.pos (p + 100)) with (Z.pos (p) + 1*100);[|auto;omega].
    rewrite Z.rem_add;[tauto|omega|simpl].
    pose (Zgt_pos_0 ((p + 100) * p));omega.
  - rewrite <- Pos2Z.add_pos_neg.
    pose (x := 100 + Z.neg p).
    assert (Z.neg p = x - 100) as ZNPEQ by (subst x; omega).
    rewrite ZNPEQ.
    replace (100 + (x - 100)) with x;[|omega].
    assert (x - 100 < 0) by (pose (Zlt_neg_0 p); subst x; omega).
    cut (if x <? 0 then x < 0 else x >= 0); [|apply Zlt_cases].
    destruct (x<?0).
    + intro XLT0.
      replace (x - 100) with (x + (-1)*100);[|omega].
      rewrite Z.rem_add.
      omega.
      omega.
      replace ((x + -1 * 100) * x) with ((-1)*(x + -1 * 100) *((-1)*x));[|lia].
      apply Zmult_gt_0_le_0_compat.
      omega.
      omega.
    + intro XGE0.
      replace (x - 100) with (-(100 - x));[|omega].
      rewrite Z.rem_opp_l;[|omega].
      assert (x < 100) as XLT100 by omega.
      replace (Z.rem x 100) with x;[|symmetry;apply Z.rem_small;omega].
      destruct x.
      * simpl; tauto.
      * assert (-Z.rem (100 - Z.pos p0) 100 + 100 = Z.pos p0) as REWR.
        rewrite Z.rem_small.
        omega.
        pose (Zgt_pos_0 p0);omega.
        rewrite REWR.
        replace (Z.pos p0 + 100) with (Z.pos p0 + 1*100);[|omega].
        apply Z.rem_add.
        omega.
        simpl.
        pose (Zgt_pos_0 ((p0 + 100) * p0));omega.
      * pose (Zlt_neg_0 p0);omega.
Qed.

Lemma loop_n100_nat: forall k n, loop k = loop (k + 100*(Z.of_nat n)).
Proof.
  intros.
  induction n.
  replace (k + 100*Z.of_nat 0) with k;[tauto|simpl;omega].
  transitivity (loop (k + 100 * Z.of_nat n)).
  assumption.
  transitivity (loop (k + 100*Z.of_nat n + 100)).
  symmetry.
  apply loop_100.
  apply f_equal.
  rewrite Nat2Z.inj_succ.
  omega.
Qed.

Lemma loop_x100: forall k x, loop k = loop (k + 100*x).
Proof.
  intros.
  induction x.
  - replace (k + 100*0) with k;[tauto|omega].
  - replace (Z.pos p) with (Z.of_nat (Pos.to_nat p));[|apply positive_nat_Z].
    apply loop_n100_nat.
  - pose (x := k + 100 * Z.neg p).
    assert (k = x + 100 * Z.pos p) as REWR.
    subst x.
    replace (Z.neg p) with (- Z.pos p);[omega|apply Pos2Z.opp_pos].
    rewrite REWR.
    rewrite <- Pos2Z.opp_pos.
    replace (x + 100 * Z.pos p + 100 * - Z.pos p) with x;[|omega].
    symmetry.
    replace (Z.pos p) with (Z.of_nat (Pos.to_nat p));[|apply positive_nat_Z].
    apply loop_n100_nat.
Qed.

Lemma loop_small : forall k, 0 <= k < 100 -> loop k = k.
Proof.
  intros.
  unfold loop.
  replace (Z.rem k 100) with k;[|symmetry;apply Z.rem_small;assumption].
  replace (k + 100) with (k + 1*100);[|omega].
  rewrite Z.rem_add;[|omega|nia].
  apply Z.rem_small;assumption.
Qed.

Lemma Repr_in_0_100: forall k, exists x, 0 <= k + 100*x < 100.
Proof.
  intros.
  destruct k.
  - exists 0;omega.
  - exists (-(Z.pos p/100)).
    assert ((Z.pos p + 100 * - (Z.pos p / 100)) = 
             Z.pos p mod 100) as REWR.
    assert (Z.pos p = 100 * (Z.pos p / 100) + Z.pos p mod 100) as TMP.
    apply Z_div_mod_eq;omega.
    omega.
    rewrite REWR.
    apply Z_mod_lt;omega.
  - exists (-(Z.neg p / 100)).
    assert (Z.neg p + 100 * - (Z.neg p / 100) = Z.neg p mod 100) as REWR.
    replace (Z.neg p + 100 * - (Z.neg p / 100))
    with (Z.neg p - Z.neg p / 100 * 100);[symmetry;apply Zmod_eq;omega|omega].
    rewrite REWR.
    apply Z_mod_lt;omega.
Qed.

Lemma Loop_bound: forall k, 0 <= loop k < 100.
Proof.
  intro.
  elim (Repr_in_0_100 k).
  intros.
  replace (loop k) with (loop (k + 100 * x));[|symmetry;apply loop_x100].
  rewrite loop_small.
  omega.
  omega.
Qed.  

Lemma amFindEmptyOnEmpty: forall m k, busybits m (loop (1 + k)) = false ->
                                      find_empty m k 100 <> None.
Proof.
  intros.
  rewrite find_empty_equation.
  rewrite loop_100.
  rewrite H.
  discriminate.
Qed.

Lemma amFindEmptyOnNext: forall m k i, find_empty m k i <> None ->
                                       find_empty m k (S i) <> None.
Proof.
  intros.
  rewrite find_empty_equation.
  destruct (busybits m (loop (1 + k + Z.of_nat (S i)))).
  assumption.
  discriminate.
Qed.

Lemma amFindEmptyOnAnyNext: 
  forall m (k : Z) (i n : nat), find_empty m k i <> None ->
                                find_empty m k (i + n) <> None.
Proof.
  intros.
  induction n.
  - assert (i + 0 = i)%nat as TMP by (simpl;omega); rewrite TMP.
    assumption.
  - replace (i + (S n))%nat with (S (i + n))%nat;[|omega].
    apply amFindEmptyOnNext.
    assumption.
Qed.

Lemma amFindEmptySameForEach100: forall m k n (i:nat),
                                      find_empty m k i = 
                                      find_empty m (k + 100*n) i.
Proof.
  intros.
  induction i;(
      rewrite find_empty_equation;
      symmetry;
      rewrite find_empty_equation
    ).
  - assert (loop (1 + (k + 100*n) + Z.of_nat 0) = loop (1 + k + 0)) as REWR. {
      replace (1 + (k + 100 * n) + Z.of_nat 0) with ((1 + k) + 100*n);[|lia].
      replace (1 + k + 0) with (1 + k);[|omega].
      symmetry;apply loop_x100.
    }
    rewrite REWR; auto.
  - assert (loop (1 + (k + 100*n) + Z.of_nat (S i)) =
            loop (1 + k + Z.of_nat (S i))) as REWR. {
      replace (1 + (k + 100 * n) + Z.of_nat (S i))
      with (1 + k + Z.of_nat (S i) + 100 * n);[|omega].
      symmetry; apply loop_x100.
    }
    rewrite REWR.
    destruct (busybits m (loop (1 + k + Z.of_nat (S i)))).
    symmetry; apply IHi.
    tauto.
Qed.

Lemma amFindEmptyStartingFromPrev:
  forall m k (i:nat), find_empty m k i <> None ->
                      find_empty m (k - 1) (S i) <> None.
Proof.
  intros.
  induction i.
  - rewrite find_empty_equation.
    rewrite find_empty_equation in H.
    replace (1 + (k - 1) + Z.of_nat 1) with (1 + k + Z.of_nat 0); [|lia].
    destruct (busybits m (loop (1 + k + Z.of_nat 0))).
    tauto.
    apply H.
  - rewrite find_empty_equation.
    rewrite find_empty_equation in H.
    replace (1 + (k - 1) + Z.of_nat (S (S i)))
    with (1 + k + Z.of_nat (S i));[|lia].
    destruct (busybits m (loop (1 + k + Z.of_nat (S i))));[|discriminate].
    apply IHi.
    apply H.
Qed.

Lemma amFindEmptyStartingFromAnyPrev:
  forall m k (i:nat) (x:nat), find_empty m k i <> None ->
                              find_empty m (k - Z.of_nat x) (i + x) <> None.
Proof.
  intros.
  induction x.
  - replace (k - Z.of_nat 0) with k; [|simpl;omega].
    replace (i + 0)%nat with i; [|simpl;omega].
    apply H.
  - replace (k - Z.of_nat (S x)) with (k - Z.of_nat x - 1);[|lia].
    replace (i + S x)%nat with (S (i + x))%nat;[|omega].
    apply amFindEmptyStartingFromPrev.
    apply IHx.
Qed.

Lemma amFindEmpty99NoLess:
  forall m k (i:nat), (i < 100)%nat -> find_empty m k i <> None ->
                find_empty m k 99 <> None.
Proof.
  intros.
  pose (x:= (99 - i)%nat).
  replace 99%nat with (i + x)%nat;[|subst x; omega].
  apply amFindEmptyOnAnyNext.
  assumption.
Qed.

(* Done so far *)

Lemma amFindEmpty99orMore:
  forall m k (n:nat), find_empty m k (99 + n) <> None ->
                      find_empty m k 99 <> None \/ 
                      find_empty m k n <> None.
Proof.
  intros.
  induction n.
  - auto.
  - rewrite find_empty_equation in H.
    replace (1 + k + Z.of_nat (99 + S n))
    with (k + Z.of_nat (S n) + 100) in H;[|lia].
    replace (loop (k + Z.of_nat (S n) + 100))
    with (loop (k + Z.of_nat (S n))) in H;[|symmetry; apply loop_100].
    destruct (busybits m (loop (k + Z.of_nat (S n)))) eqn: BB.
    + replace (99 + S n)%nat with (S (99 + n))%nat in H;[|omega].
      apply IHn in H.
      decompose sum H.
      * left;assumption.
      * right;apply amFindEmptyOnNext;assumption.
    + right.
      rewrite find_empty_equation.
      destruct (busybits m (loop (1 + k + Z.of_nat (S n)))).
      * rewrite find_empty_equation.
        replace (1 + k + Z.of_nat n)
        with (k + Z.of_nat (S n));[|lia].
        rewrite BB.
        discriminate.
      * discriminate.
Qed.

Lemma amFindEmpty99PlusABit:
  forall m k (n x:nat), find_empty m k (99*x + n) <> None ->
                        find_empty m k 99 <> None \/
                        find_empty m k n <> None.
Proof.
  intros.
  induction x.
  - auto.
  - replace (99 * S x + n)%nat 
    with (99 + 99*x + n)%nat in H; [|omega].
    apply amFindEmpty99orMore with (n:=(99*x + n)%nat) in H.
    decompose sum H.
    + left; assumption.
    + apply IHx; assumption.
Qed.

Lemma amFindEmpty99IsEnough:
  forall m k (n:nat), find_empty m k n <> None ->
                      find_empty m k 99 <> None.
Proof.
  intros.
  pose (x := Z.to_nat ((Z.of_nat n)/99)).
  pose (r := Z.to_nat ((Z.of_nat n) mod 99)).
  assert (n = (99*x + r)%nat) as REPR. {
    subst x r.
    SearchAbout Z.of_nat.
    assert (n = Z.to_nat (Z.of_nat n)) as N2Z by (symmetry;apply Nat2Z.id).
    rewrite N2Z at 1.
    assert (99 = Z.to_nat (Z.of_nat 99))%nat as TMP by auto.
    rewrite TMP at 1.
    pose (Zle_0_nat n).
    pose (Zle_0_nat 99).
    assert (0 <= Z.of_nat n / 99) by (apply Z_div_pos;omega).
    rewrite <- Z2Nat.inj_mul;[|omega|auto].
    rewrite <- Z2Nat.inj_add;
      [|apply Z.mul_nonneg_nonneg;omega|apply Z_mod_lt;omega].
    apply f_equal.
    apply Z_div_mod_eq;omega.
  }
  assert (r < 99)%nat. {
    subst r.
    replace 99%nat with (Z.to_nat 99);[|auto].
    apply Z2Nat.inj_lt;[|omega|];apply Z_mod_lt;omega.
  }
  rewrite REPR in H.
  apply amFindEmpty99PlusABit in H.
  decompose sum H.
  - tauto.
  - apply amFindEmpty99NoLess with r;[omega|assumption].
Qed.
    
Lemma amFindEmptyStartingAnywhere:
  forall m k x, 0 <= x -> find_empty m k 99 <> None ->
                find_empty m (k - x) 99 <> None.
Proof.
  intros m k x XLE0 H.
  apply amFindEmptyStartingFromAnyPrev with (x:=Z.to_nat x) in H.
  replace (Z.of_nat (Z.to_nat x)) with x in H.
  apply amFindEmpty99IsEnough in H.
  assumption.
  destruct x.
  - auto.
  - symmetry; apply positive_nat_Z.
  - pose (Zlt_neg_0 p);omega.
Qed.

Check dec_Zlt.

Lemma amWillFindEmptyBehind: forall m k x i, k <= x -> find_empty m x i <> None ->
                                             find_empty m k 99 <> None.
Proof.
  intros.
  pose (d := x - k).
  assert (0 <= d) by (subst d; omega).
  replace k with (x - d);[|subst d; omega].
  apply amFindEmptyStartingAnywhere.
  - omega.
  - apply amFindEmpty99IsEnough in H0.
    assumption.
Qed.

Lemma amWillFindEmpty: forall m k x i , find_empty m x i <> None ->
                                        find_empty m k 99 <> None.
Proof.
  intros.
  pose (XLTK:=dec_Zlt x k).
  unfold Decidable.decidable in XLTK.
  decompose sum XLTK.
  - pose (a:= (k - x)/100 + 1).
    pose (b:= k - (100*a)).
    assert (b <= x). {
      subst b a.
      SearchAbout (_*(_+_)).
      rewrite Z.mul_add_distr_l.
      assert (k - x - (k - x) mod 100 = 100 * ((k - x) / 100)) as REWR. {
        pose (Z_div_mod_eq (k-x) 100).
        omega.
      }
      rewrite <- REWR.
      remember ((k - x) mod 100) as a.
      assert (0 <= a < 100) by (subst a; apply Z_mod_lt;omega).
      omega.
    }
    replace k with (b + (100*a));[|subst b;omega].
    rewrite <- amFindEmptySameForEach100.
    apply amWillFindEmptyBehind with x i;[omega|assumption].
  - apply amWillFindEmptyBehind with x i;[omega|assumption].
Qed.

Lemma amFindEmptyNotBlind: forall m k, 0 <= k < 100 ->
                                       (~is_true (busybits m k)) ->
                                       find_empty m k 99 <> None.
Proof.
  intros m k KBOUND H.
  rewrite find_empty_equation.
  replace (1 + k + Z.of_nat 99) with (k + 100);[|lia].
  rewrite loop_100.
  rewrite loop_small;[|assumption].
  unfold is_true in H.
  destruct (busybits m k).
  - tauto.
  - discriminate.
Qed.

Lemma amNonFullCanFindEmpty: forall m k, ~(full m) -> find_empty m k 99 <> None.
Proof.
  intros.
  unfold full in H.
  apply not_forall_exists in H.
  destruct H.
  remember (loop x) as k0.
  assert (0 <= k0 < 100) by (subst k0;apply Loop_bound).
  apply amWillFindEmpty with k0 99%nat.
  apply amFindEmptyNotBlind;assumption.
Qed.

Lemma amCanPut: forall m k v, ~(full m) -> amPut m k v <> None.
Proof.
  intros.
  unfold amPut.
  apply amNonFullCanFindEmpty with (k:=(loop k)) in H.
  destruct (find_empty m (loop k) 99).
  - discriminate.
  - tauto.
Qed.