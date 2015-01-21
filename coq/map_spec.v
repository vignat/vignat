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

Print well_founded.

Definition less_order (a b : Z) : Prop :=
  0 <= a < b.

Lemma less_order_nat_wf' : forall bound x:nat, (x <= bound)%nat ->
                                              Acc less_order (Z.of_nat x).
Proof.
  intro bound. (*can not intro x, because need forall quantificator in IH *)
  unfold less_order.
  induction bound;constructor;intros.
  - omega.
  - pose (z:=Z.to_nat y).
    assert (YZ: y=Z.of_nat z).
    subst z.
    destruct y.
    auto.
    simpl.
    symmetry.
    apply positive_nat_Z.
    pose (Zlt_neg_0 p); omega.
    rewrite YZ.
    apply IHbound.
    omega.
Qed.

Lemma less_order_wf' : forall x, Acc less_order x.
Proof.
  intros.
  destruct x;constructor;intros.
  - unfold less_order; unfold less_order in H; omega.
  - destruct y.
    + rewrite <- inj_0 at 1.
      apply less_order_nat_wf' with (bound:=0%nat) (x:=0%nat).
      auto.
    + unfold less_order in H.
      rewrite <- positive_nat_Z.
      apply less_order_nat_wf' with (bound:=Z.to_nat(Z.pos p)) (x:=Z.to_nat(Z.pos p0)).
      rewrite <- Z2Nat.inj_le; omega.
    + unfold less_order in H.
      pose (Zlt_neg_0 p0); omega.
  - unfold less_order in H.
    pose (Zlt_neg_0 p); omega.
Qed.

Lemma less_order_wf : well_founded less_order.
Proof.
  unfold well_founded.
  apply less_order_wf'.
Qed.

Lemma decr_wf: forall x, x > 0 -> less_order (x - 1) x.
Proof.
intros.
unfold less_order.
omega.
Qed.

Check Fix.

Require Import Recdef.

(* search goes from index + 100 down with round up from 0,
 so i runs from 100 down to 1. first checked cell is
 start + 100 = start. then
 start + 99 = start - 1 mod 100*)

Function find_empty (m : ArrMapZ) (start : Z) (i : Z) {wf less_order i}: option Z :=
  if (busybits m (loop (start + i)))
  then if (Z.ltb 1 i)
       then find_empty m start (i - 1)
       else None
  else Some (loop (start + i)).
intros.
apply decr_wf.
destruct i; [|apply Zgt_pos_0|]; discriminate teq0.
apply less_order_wf.
Defined.

Function find_key (m : ArrMapZ) (start : Z) (key : Z) (i : Z)
         {wf less_order i}: option Z :=
  if (busybits m (loop (start + i)))
  then if (Z.eq_dec key (keys m (loop (start + i))))
       then Some (loop (start + i))
       else if (Z.ltb 1 i)
            then find_key m start key (i - 1)
            else None
  else None.
intros.
apply decr_wf.
destruct i; [|apply Zgt_pos_0|]; discriminate teq1.
apply less_order_wf.
Defined.

Function amGet (map : ArrMapZ) (key : Z) : option Z :=
  match find_key map (loop key) key 100 with
    |Some index => Some (values map index)
    |None => None
  end.

Function amPut (map : ArrMapZ) (key : Z) (val : Z) : option ArrMapZ :=
  match find_empty map (loop key) 100 with
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

Definition full (m : ArrMapZ) :=
  forall i, 0 <= i < 100 -> is_true (busybits m i).

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

Check find_empty_ind.

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

Lemma amFindEmptyOnEmpty: forall m k, busybits m (loop k) = false ->
                                      find_empty m k 100 <> None.
Proof.
  intros.
  rewrite find_empty_equation.
  rewrite loop_100.
  rewrite H.
  discriminate.
Qed.

Lemma amFindEmptyOnNext: forall m k i, 0 < i -> find_empty m k i <> None ->
                                       find_empty m k (i + 1) <> None.
Proof.
  intros.
  rewrite find_empty_equation.
  destruct (busybits m (loop (k + (i + 1)))).
  assert (1 < i + 1) as TMP by omega.
  rewrite Zlt_is_lt_bool in TMP.
  rewrite TMP.
  assert (i + 1 - 1 = i) as TMP2 by omega; rewrite TMP2.
  assumption.
  discriminate.
Qed.

Lemma amFindEmptyOnAnyNextNat: 
  forall m (k i : Z) (n : nat), 0 < i ->
                                find_empty m k i <> None ->
                                find_empty m k (i + Z.of_nat n) <> None.
Proof.
  intros.
  induction n.
  - assert (i + Z.of_nat 0 = i) as TMP by (simpl;omega); rewrite TMP.
    assumption.
  - assert (i + Z.of_nat (S n) = i + Z.of_nat n + 1) as TMP.
    rewrite Nat2Z.inj_succ.
    SearchAbout Z.succ.
    rewrite <- Z.add_1_r.
    omega.
    rewrite TMP.
    apply amFindEmptyOnNext.
    omega.
    assumption.
Qed.

Lemma amFindEmptyOnAnyNext:
  forall m k i x, 0 < i -> 0 <= x -> find_empty m k i <> None ->
                  find_empty m k (i + x) <> None.
Proof.
  intros.
  pose (n := Z.to_nat x).
  assert (x = Z.of_nat n) as REWR.
  subst n.
  symmetry.
  apply Z2Nat.id.
  assumption.
  rewrite REWR.
  apply amFindEmptyOnAnyNextNat; assumption.
Qed.

Lemma amFindEmptySameForEach100Nat: forall m k (i:nat) n,
                                      find_empty m k (Z.of_nat i) =
                                      find_empty m (k + 100*n) (Z.of_nat i).
Proof.
  intros.
  induction i.
  - rewrite find_empty_equation.
    symmetry.
    rewrite find_empty_equation.
    replace (loop (k + 100*n + Z.of_nat 0)) with (loop (k + 0)).
    auto.
    replace (k + 0) with k;[|omega].
    replace (k + 100*n + Z.of_nat 0) with (k + 100*n);[|simpl;omega].
    apply loop_x100.
  - rewrite find_empty_equation.
    symmetry.
    rewrite find_empty_equation.
    assert (loop (k + 100*n + Z.of_nat (S i)) =
            loop (k + Z.of_nat (S i))) as REWR.
    replace (k + 100 * n + Z.of_nat (S i)) with (k + Z.of_nat (S i) + 100 * n).
    symmetry; apply loop_x100.
    omega.
    rewrite REWR.
    destruct (busybits m (loop (k + Z.of_nat (S i)))).
    destruct (1 <? Z.of_nat (S i)).
    replace (Z.of_nat (S i) - 1) 
    with (Z.of_nat i);[|rewrite Nat2Z.inj_succ;omega].
    symmetry; apply IHi.
    tauto.
    tauto.
Qed.

Lemma amFindEmptySameForEach100: forall m k i n, 0 <= i ->
                                   find_empty m k i =
                                   find_empty m (k + 100*n) i.
Proof.
  intros.
  pose (z:=Z.to_nat i).
  assert (IZ: i=Z.of_nat z). {
    subst z.
    destruct i.
    - auto.
    - simpl; symmetry; apply positive_nat_Z.
    - pose (Zlt_neg_0 p); omega.
  }
  rewrite IZ.
  apply amFindEmptySameForEach100Nat.
Qed.

Lemma amFindEmptyStartingFromPrevNat:
  forall m k (i:nat), find_empty m k (Z.of_nat i) <> None ->
                      find_empty m (k - 1) (Z.of_nat (i + 1)) <> None.
Proof.
  intros.
  induction i.
  - rewrite find_empty_equation.
    simpl.
    rewrite find_empty_equation in H.
    simpl in H.
    replace (k - 1 + 1) with (k + 0); [|omega].
    apply H.
  - rewrite find_empty_equation.
    rewrite find_empty_equation in H.
    replace (k - 1 + Z.of_nat (S i + 1)) with (k + Z.of_nat (S i));[|lia].
    destruct (busybits m (loop (k + Z.of_nat (S i))));[|discriminate].
    destruct i.
    + simpl in H; tauto.
    + assert (is_true (1 <? Z.of_nat (S (S i)))) as REWR.
      destruct (1 <? Z.of_nat (S (S i))); [auto|tauto].
      rewrite REWR in H.
      replace (Z.of_nat (S (S i)) - 1) with (Z.of_nat (S i)) in H.
      apply IHi in H.
      replace (Z.of_nat (S (S i) + 1) - 1) with (Z.of_nat (S i + 1)).
      cut (if 1 <? Z.of_nat (S (S i) + 1)
           then 1 < Z.of_nat (S (S i) + 1)
           else 1 >= Z.of_nat (S (S i) + 1)); [|apply Zlt_cases].
      destruct (1 <? Z.of_nat (S (S i) + 1)). 
      intro.
      apply H.
      intro.
      lia.
      lia.
      lia.
Qed.

Lemma amFindEmptyStartingFromAnyPrevNat:
  forall m k (i:nat) (x:nat), find_empty m k (Z.of_nat i) <> None ->
                              find_empty m (k - Z.of_nat x) (Z.of_nat (i + x)) <> None.
Proof.
  intros.
  induction x.
  - replace (k - Z.of_nat 0) with k; [|simpl;omega].
    replace (i + 0)%nat with i; [|simpl;omega].
    apply H.
  - replace (k - Z.of_nat (S x)) with (k - Z.of_nat x - 1);[|lia].
    replace (i + S x)%nat with (i + x + 1)%nat;[|omega].
    apply amFindEmptyStartingFromPrevNat.
    apply IHx.
Qed.

(* Done so far *)

Lemma amFindEmpty100NoLess:
  forall m k i, 0 < i <= 100 -> find_empty m k i <> None ->
                find_empty m k 100 <> None.
Proof.
  intros.
  pose (x:= 100 - i).
  replace 100 with (i + x);[|subst x; omega].
  apply amFindEmptyOnAnyNext.
  omega.
  subst x;omega.
  assumption.
Qed.

Lemma amFindEmpty100IsEnough:
  forall m k i, 100 < i -> find_empty m k i <> None ->
                find_empty m k 100 <> None.
Proof.
  intros.
  pose (x := 
  

Lemma amFindEmptyStartingAnywhere:
  forall m k x, find_empty m k 100 <> None ->
                find_empty m (k - x) 100 <> None.
Proof.
  intros.
  

Lemma amWillFindEmpty: forall m k x i, find_empty m x 100 <> None ->
                                       find_empty m k 100 <> None.
Proof.
  intros.
  pose (d:=k - x
  

Lemma amNonFullCanFindEmpty: forall m k, ~(full m) -> find_empty m k 100 <> None.
Proof.
  intros.
  unfold full in H.
  apply not_forall_exists in H.
  destruct H.
  unfold find_empty.
  unfold find_empty_terminate.
  
Lemma amCanPut: forall m k v, ~(full m) -> amPut m k v <> None.
Proof.
  intros.

  