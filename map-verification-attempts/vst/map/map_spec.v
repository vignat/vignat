Require Import Coq.ZArith.Zbool.
Require Import Coq.ZArith.BinInt.
Require Import ZArith.ZArith_dec.
Require Import ZArith.ZArith_base.
Require Import ZArith.Zdiv.
Require Import Coq.Setoids.Setoid.
Require Import Classical.
Require Import Psatz.
Require Import FunctionalExtensionality.

Local Open Scope Z.

Function loop (k:Z): Z :=
  Z.rem ((Z.rem k 100) + 100) 100.

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

Function find_if (cond : Z -> bool) (start : Z) (i : nat): option Z :=
  if (cond (loop (1 + start + Z.of_nat i)))
  then Some (loop (1 + start + Z.of_nat i))
  else match i with
         | S p => find_if cond start p
         | O => None
       end.

Function find_empty (m : ArrMapZ) (start : Z) (i : nat): option Z :=
  find_if (fun k => negb (busybits m k)) start i.

Function find_key (m : ArrMapZ) (start : Z) (key : Z) (i : nat): option Z :=
  find_if (fun k => andb (busybits m k)
                         (Z.eqb key (keys m k)))
          start i.

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

Function amErase (map : ArrMapZ) (key : Z) : option ArrMapZ :=
  match find_key map (loop key) key 99 with
    |Some index => Some {|values:= values map;
                          keys:= keys map;
                          busybits:= (fun (i:Z) =>
                                        if (Z.eq_dec i index)
                                        then false
                                        else busybits map i) |}
    |None => None
  end.

Function amPartSize(m:ArrMapZ)(i:nat) : nat :=
  match i with
    |S p => ((if (busybits m (Z.of_nat p)) then 1 else 0) +
            amPartSize m p)%nat
    |O => O
  end.

Function amSize(m:ArrMapZ) : nat := amPartSize m 100.


Definition full (m : ArrMapZ):Prop :=
  forall k, is_true (busybits m (loop k)).

Definition contains (m : ArrMapZ) (k : Z) :=
  exists x, 0 <= x < 100 /\ is_true (busybits m x) /\ keys m x = k.

Definition contains_single (m : ArrMapZ) (k : Z) :=
  contains m k /\ forall x y, 0 <= x < 100 -> 0 <= y < 100 ->
                              is_true(busybits m x) ->
                              is_true(busybits m y) ->
                              keys m x = k ->
                              keys m y = k ->
                              y = x.

Definition nodups(map:ArrMapZ) :Prop :=
  forall x y, 0 <= x < 100 -> 0 <= y < 100 -> busybits map x = true ->
              busybits map y = true -> keys map x = keys map y -> x = y.


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

Lemma amFindIfOnNext: forall cond k i, find_if cond k i <> None ->
                                       find_if cond k (S i) <> None.
Proof.
  intros.
  rewrite find_if_equation.
  destruct (cond (loop (1 + k + Z.of_nat (S i)))).
  discriminate.
  assumption.
Qed.

Lemma amFindIfOnAnyNext:
  forall c (k : Z) (i n : nat), find_if c k i <> None ->
                                find_if c k (i + n) <> None.
Proof.
  intros.
  induction n.
  - assert (i + 0 = i)%nat as TMP by (simpl;omega); rewrite TMP.
    assumption.
  - replace (i + (S n))%nat with (S (i + n))%nat;[|omega].
    apply amFindIfOnNext.
    assumption.
Qed.

Lemma amFindIfSameForEach100: forall cond k n (i:nat),
                                find_if cond k i =
                                find_if cond (k + 100*n) i.
Proof.
  intros.
  induction i;(
      rewrite find_if_equation;
      symmetry;
      rewrite find_if_equation
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
    destruct (cond (loop (1 + k + Z.of_nat (S i)))).
    tauto.
    symmetry; apply IHi.
Qed.

Lemma amFindIfStartingFromPrev:
  forall cond k (i:nat), find_if cond k i <> None ->
                         find_if cond (k - 1) (S i) <> None.
Proof.
  intros.
  induction i;(
      rewrite find_if_equation;
      rewrite find_if_equation in H
    ).
  - replace (1 + (k - 1) + Z.of_nat 1) with (1 + k + Z.of_nat 0); [|lia].
    destruct (cond (loop (1 + k + Z.of_nat 0))); tauto.
  - replace (1 + (k - 1) + Z.of_nat (S (S i)))
    with (1 + k + Z.of_nat (S i));[|lia].
    destruct (cond (loop (1 + k + Z.of_nat (S i))));tauto.
Qed.

Lemma amFindIfStartingFromAnyPrev:
  forall cond k (i:nat) (x:nat), find_if cond k i <> None ->
                                 find_if cond (k - Z.of_nat x) (i + x) <> None.
Proof.
  intros.
  induction x.
  - replace (k - Z.of_nat 0) with k; [|simpl;omega].
    replace (i + 0)%nat with i; [|simpl;omega].
    apply H.
  - replace (k - Z.of_nat (S x)) with (k - Z.of_nat x - 1);[|lia].
    replace (i + S x)%nat with (S (i + x))%nat;[|omega].
    apply amFindIfStartingFromPrev.
    apply IHx.
Qed.

Lemma amFindIf99NoLess:
  forall cond k (i:nat), (i < 100)%nat -> find_if cond k i <> None ->
                         find_if cond k 99 <> None.
Proof.
  intros.
  pose (x:= (99 - i)%nat).
  replace 99%nat with (i + x)%nat;[|subst x; omega].
  apply amFindIfOnAnyNext.
  assumption.
Qed.

Lemma amFindIf99orMore:
  forall cond k (n:nat), find_if cond k (99 + n) <> None ->
                         find_if cond k 99 <> None \/
                         find_if cond k n <> None.
Proof.
  intros.
  induction n.
  - auto.
  - rewrite find_if_equation in H.
    replace (1 + k + Z.of_nat (99 + S n))
    with (k + Z.of_nat (S n) + 100) in H;[|lia].
    replace (loop (k + Z.of_nat (S n) + 100))
    with (loop (k + Z.of_nat (S n))) in H;[|symmetry; apply loop_100].
    destruct (cond (loop (k + Z.of_nat (S n)))) eqn: BB.
    + right.
      rewrite find_if_equation.
      destruct (cond (loop (1 + k + Z.of_nat (S n)))).
      * discriminate.
      * rewrite find_if_equation.
        replace (1 + k + Z.of_nat n)
        with (k + Z.of_nat (S n));[|lia].
        rewrite BB.
        discriminate.
    + replace (99 + S n)%nat with (S (99 + n))%nat in H;[|omega].
      apply IHn in H.
      decompose sum H.
      * left;assumption.
      * right;apply amFindIfOnNext;assumption.
Qed.

Lemma amFindIf99PlusABit:
  forall cond k (n x:nat), find_if cond k (99*x + n) <> None ->
                           find_if cond k 99 <> None \/
                           find_if cond k n <> None.
Proof.
  intros.
  induction x.
  - auto.
  - replace (99 * S x + n)%nat
    with (99 + 99*x + n)%nat in H; [|omega].
    apply amFindIf99orMore with (n:=(99*x + n)%nat) in H.
    decompose sum H.
    + left; assumption.
    + apply IHx; assumption.
Qed.

Lemma amFindIf99IsEnough:
  forall cond k (n:nat), find_if cond k n <> None ->
                         find_if cond k 99 <> None.
Proof.
  intros.
  pose (x := Z.to_nat ((Z.of_nat n)/99)).
  pose (r := Z.to_nat ((Z.of_nat n) mod 99)).
  assert (n = (99*x + r)%nat) as REPR. {
    subst x r.
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
  apply amFindIf99PlusABit in H.
  decompose sum H.
  - tauto.
  - apply amFindIf99NoLess with r;[omega|assumption].
Qed.

Lemma amFindIfStartingAnywhere:
  forall cond k x, 0 <= x -> find_if cond k 99 <> None ->
                   find_if cond (k - x) 99 <> None.
Proof.
  intros m k x XLE0 H.
  apply amFindIfStartingFromAnyPrev with (x:=Z.to_nat x) in H.
  replace (Z.of_nat (Z.to_nat x)) with x in H.
  apply amFindIf99IsEnough in H.
  assumption.
  destruct x.
  - auto.
  - symmetry; apply positive_nat_Z.
  - pose (Zlt_neg_0 p);omega.
Qed.

Lemma amWillFindIfBehind:
  forall cond k x i, k <= x -> find_if cond x i <> None ->
                     find_if cond k 99 <> None.
Proof.
  intros.
  pose (d := x - k).
  assert (0 <= d) by (subst d; omega).
  replace k with (x - d);[|subst d; omega].
  apply amFindIfStartingAnywhere.
  - omega.
  - apply amFindIf99IsEnough in H0.
    assumption.
Qed.

Lemma amWillFindIf: forall cond k x i , find_if cond x i <> None ->
                                        find_if cond k 99 <> None.
Proof.
  intros.
  pose (XLTK:=dec_Zlt x k).
  unfold Decidable.decidable in XLTK.
  decompose sum XLTK.
  - pose (a:= (k - x)/100 + 1).
    pose (b:= k - (100*a)).
    assert (b <= x). {
      subst b a.
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
    rewrite <- amFindIfSameForEach100.
    apply amWillFindIfBehind with x i;[omega|assumption].
  - apply amWillFindIfBehind with x i;[omega|assumption].
Qed.

Lemma amFindIfNotBlind: forall cond k, 0 <= k < 100 ->
                                       is_true (cond k) ->
                                       find_if cond k 99 <> None.
Proof.
  intros cond k KBOUND H.
  rewrite find_if_equation.
  replace (1 + k + Z.of_nat 99) with (k + 100);[|lia].
  rewrite loop_100.
  rewrite loop_small;[|assumption].
  unfold is_true in H.
  rewrite H.
  discriminate.
Qed.

Lemma amFindIfBound: forall cond k i, match (find_if cond k i) with
                                        | Some z => 0 <= z < 100
                                        | None => True
                                      end.
Proof.
  intros.
  rewrite find_if_equation.
  induction i.
  - destruct (cond (loop (1 + k + Z.of_nat 0))).
    + apply Loop_bound.
    + tauto.
  - rewrite <- find_if_equation in IHi.
    destruct (cond (loop (1 + k + Z.of_nat (S i)))).
    + apply Loop_bound.
    + apply IHi.
Qed.

Lemma amFindIfCorrect: forall cond s i, match (find_if cond s i) with
                                            |Some z => is_true (cond z)
                                            |None => True
                                        end.
Proof.
  intros.
  rewrite find_if_equation.
  induction i.
  - destruct (cond (loop (1 + s + Z.of_nat 0))) eqn: COND; auto.
  - rewrite <- find_if_equation in IHi.
    destruct (cond (loop (1 + s + Z.of_nat (S i)))) eqn: COND; auto.
Qed.
Lemma isKeyEquivalence: forall m k key,
                          (is_true (busybits m k) /\
                           keys m k = key) <->
                          is_true(andb (busybits m k)
                                       (Z.eqb key (keys m k))).
Proof.
  intros.
  split.
  - intro.
    destruct H as [BB EQ].
    unfold is_true in BB.
    rewrite BB.
    rewrite EQ.
    unfold is_true;simpl.
    apply Z.eqb_eq.
    tauto.
  - intro.
    unfold is_true in H.
    apply Bool.andb_true_iff in H.
    destruct H as [BB EQ].
    rewrite BB.
    split;auto.
    symmetry;apply Z.eqb_eq;assumption.
Qed.

Lemma amFindEmptyBound: forall m s i, match (find_empty m s i) with
                                        |Some z => 0 <= z < 100
                                        |None => True
                                      end.
Proof.
  intros.
  unfold find_empty.
  apply amFindIfBound.
Qed.

Lemma amFindEmptyCorrect: forall m s i, match (find_empty m s i) with
                                          |Some z => (busybits m z = false)
                                          |None => True
                                        end.
Proof.
  intros.
  destruct (find_empty m s i) eqn: Heqfe;[|tauto].
  unfold find_empty in Heqfe.
  pose (amFindIfCorrect
          (fun k : Z => negb (busybits m k)) s i) as FIC.
  rewrite Heqfe in FIC.
  destruct (busybits m z);auto.
Qed.

Lemma amFindKeyBound: forall m k s i, match (find_key m s k i) with
                                         |Some z => 0 <= z < 100
                                         |None => True
                                     end.
Proof.
  intros; unfold find_key; apply amFindIfBound.
Qed.

Lemma amNonFullCanFindEmpty: forall m k, ~(full m) <-> find_empty m k 99 <> None.
Proof.
  split; intro.
  - unfold full in H.
    apply not_forall_exists in H.
    destruct H.
    remember (loop x) as k0.
    assert (0 <= k0 < 100) by (subst k0;apply Loop_bound).
    unfold find_empty.
    apply amWillFindIf with (x:=k0) (i:=99%nat).
    apply amFindIfNotBlind.
    + assumption.
    + destruct (busybits m k0); auto.
  - unfold full.
    assert (FEC:=amFindEmptyCorrect m k 99).
    assert (FEB:=amFindEmptyBound m k 99).
    destruct (find_empty m k 99) eqn:FE;[|tauto].
    contradict FEC.
    unfold is_true in FEC.
    rewrite <- loop_small with z;[|omega].
    rewrite FEC.
    discriminate.
Qed.

Lemma amCanPut: forall m k v, ~(full m) <-> amPut m k v <> None.
Proof.
  split;intro.
  - unfold amPut.
    apply amNonFullCanFindEmpty with (k:=(loop k)) in H.
    destruct (find_empty m (loop k) 99).
    + discriminate.
    + tauto.
  - rewrite amNonFullCanFindEmpty.
    unfold amPut in H.
    instantiate (1:=(loop k)).
    destruct (find_empty m (loop k) 99).
    + discriminate.
    + tauto.
Qed.


Lemma amPutContains: forall m k v, ~(full m) -> match (amPut m k v) with
                                                    |Some map => contains map k
                                                    |None => False
                                                end.
Proof.
  intros.
  rewrite amCanPut in H.
  destruct (amPut m k v) eqn: PUT.
  - unfold contains.
    remember (find_empty m (loop k) 99) as found.
    pose (amFindEmptyBound m (loop k) 99) as FEbound.
    destruct found.
    + rewrite <- Heqfound in FEbound.
      exists z.
      constructor.
      * apply FEbound.
      * unfold amPut in PUT.
        rewrite <- Heqfound in PUT.
        injection PUT as P.
        rewrite <- P.
        simpl.
        destruct (Z.eq_dec z z);auto;constructor;[auto|tauto].
    + unfold amPut in PUT.
      rewrite <- Heqfound in PUT.
      discriminate PUT.
  - instantiate (1:=v) in H; instantiate (1:=k) in H; tauto.
Qed.


Lemma amFindKeyCorrect: forall m k s i, match (find_key m s k i) with
                                        |Some z => is_true (busybits m z) /\
                                                   keys m z = k
                                        |None => True
                                      end.
Proof.
  intros.
  destruct (find_key m s k i) eqn: Heqfk.
  unfold find_key in Heqfk.
  - pose (amFindIfCorrect
            (fun k0:Z => (busybits m k0 && (k =? keys m k0))%bool)
            s i) as FIC.
    simpl in FIC.
    rewrite Heqfk in FIC.
    apply isKeyEquivalence;assumption.
  - tauto.
Qed.

Lemma amContainsCanFindKey: forall m k s, contains m k <->
                                          find_key m s k 99 <> None.
Proof.
  split;intro.
  - unfold contains in H.
    destruct H.
    destruct H as [BOUND COND].
    unfold find_key.
    apply amWillFindIf with (x:=x) (i:=99%nat).
    apply amFindIfNotBlind.
    + assumption.
    + apply isKeyEquivalence;assumption.
  - assert (CORR:=amFindKeyCorrect m k s 99).
    assert (BND:=amFindKeyBound m k s 99).
    destruct (find_key m s k 99) eqn:FK;[|tauto].
    unfold contains.
    exists z;intuition.
Qed.

Lemma amCanGet: forall m k, contains m k <-> amGet m k <> None.
Proof.
  split;intros.
  - unfold amGet.
    apply amContainsCanFindKey with (s:=loop k) in H.
    destruct (find_key m (loop k) k 99).
    + discriminate.
    + assumption.
  - rewrite amContainsCanFindKey with (s:=(loop k)).
    unfold amGet in H.
    destruct (find_key m (loop k) k 99).
    + discriminate.
    + assumption.
Qed.

Lemma amFindExactKey: forall m k s x,
                        0 <= x < 100 ->
                        (keys m x = k) ->
                        is_true (busybits m x) ->
                        (forall y, y <> x ->
                                   ~(0 <= y < 100 /\ is_true (busybits m y) /\
                                     (keys m y = k))) ->
                        match (find_key m s k 99) with
                          |Some z => z = x
                          |None => False
                        end.
Proof.
  intros m k s x BOUND KEY BUSY UNIQUE.
  assert (FRK := amFindKeyCorrect m k s 99).
  destruct (find_key m s k 99) eqn: Heqfk.
  - specialize UNIQUE with z.
    destruct (Z.eq_dec z x).
    + assumption.
    + apply UNIQUE in n.
      pose (amFindKeyBound m k s 99) as FKbound.
      rewrite Heqfk in FKbound.
      contradict n.
      intuition.
  - assert (contains m k) as CONT. {
      unfold contains.
      exists x.
      auto.
    }
    apply amContainsCanFindKey with (s:=s) in CONT.
    unfold amGet in CONT.
    rewrite Heqfk in CONT.
    tauto.
Qed.


Theorem amGetPut1: forall m k v, ~(full m) ->
                                 ~(contains m k) ->
                                 match (amPut m k v) with
                                   |Some map => amGet map k = Some v
                                   |None => False
                                 end.
Proof.
  intros m k v NONFULL ABSCENT.
  rewrite amCanPut in NONFULL.
  destruct (amPut m k v) eqn: PUT'.
  - unfold amGet.
    unfold amPut in PUT'.
    destruct (find_empty m (loop k) 99) eqn: FE;[|discriminate].
    injection PUT' as PUT.
    rename z into x.
    rename a into map.
    assert (FEB:=amFindEmptyBound m (loop k) 99).
    rewrite FE in FEB.
    assert (keys map x = k) as EQ. {
      rewrite <- PUT.
      simpl.
      destruct (Z.eq_dec x x);[auto|tauto].
    }
    assert (is_true (busybits map x)) as BB. {
      rewrite <- PUT;simpl;destruct (Z.eq_dec x x);[auto|tauto].
    }
    assert (forall y : Z,
              y <> x ->
              ~ (0 <= y < 100 /\ is_true (busybits map y) /\
                 keys map y = k)) as UNIQUE. {
      intros.
      unfold contains in ABSCENT.
      contradict ABSCENT.
      exists y.
      rewrite <- PUT in ABSCENT; simpl in ABSCENT.
      destruct (Z.eq_dec y x);tauto.
    }
    assert (FEK:= amFindExactKey map k (loop k) x FEB EQ BB UNIQUE).
    destruct (find_key map (loop k) k 99).
    * rewrite <- PUT. simpl. rewrite FEK.
      destruct (Z.eq_dec x x); tauto.
    * tauto.
  - instantiate (1:=v) in NONFULL; instantiate (1:=k) in NONFULL; tauto.
Qed.

Theorem amGetPut2: forall m k1 k2 v, ~(full m) -> k1 <> k2 ->
                                     match (amPut m k1 v) with
                                       |Some map => amGet map k2 = amGet m k2
                                       |None => False
                                     end.
Proof.
  intros m k1 k2 v NONFULL NEQ.
  rewrite (amCanPut m k1 v) in NONFULL.
  destruct (amPut m k1 v) eqn: PUT';[|tauto].
  unfold amPut in PUT'.
  destruct (find_empty m (loop k1) 99) eqn: FE;
    [|symmetry in PUT';contradiction].
  rename z into ind, a into map.
  injection PUT' as PUT.
  unfold amGet.
  assert (FEC:=amFindEmptyCorrect m (loop k1) 99).
  rewrite FE in FEC.
  assert (forall k, ((busybits map k && (k2 =? keys map k)) =
                     (busybits m k && (k2 =? keys m k))))%bool as EQCOND. {
    intro.
    rewrite <- PUT.
    simpl.
    destruct (Z.eq_dec k ind) eqn: KIND.
    - replace (k2 =? k1) with false;[|symmetry;apply Z.eqb_neq;auto].
      subst k.
      rewrite FEC.
      auto.
    - tauto.
  }
  apply functional_extensionality in EQCOND.
  unfold find_key.
  rewrite EQCOND.
  replace (find_if (fun k : Z =>
                      (busybits m k && (k2 =? keys m k))%bool) (loop k2) 99)
  with (find_key m (loop k2) k2 99);[|unfold find_key;tauto].
  destruct (find_key m (loop k2) k2 99) eqn: Heqfk;[|tauto].
  pose (FRK:=amFindKeyCorrect m k2 (loop k2) 99).
  rewrite Heqfk in FRK.
  destruct FRK as [BB EQ].
  rewrite <- PUT.
  simpl.
  destruct (Z.eq_dec z ind);[|tauto].
  unfold is_true in BB.
  subst z.
  rewrite FEC in BB.
  discriminate BB.
Qed.

Lemma amPutMore: forall m k v, ~(full m) -> contains m k ->
                                 match (amPut m k v) with
                                     |Some map => ~(contains_single map k)
                                     |None => False
                                 end.
Proof.
  intros m k v NONFULL HAS.
  rewrite (amCanPut m k v) in NONFULL.
  destruct (amPut m k v) eqn:PUT';[|tauto].
  unfold amPut in PUT'.
  destruct (find_empty m (loop k) 99) eqn: FE;
    [|symmetry in PUT';contradiction].
  injection PUT' as PUT.
  unfold contains in HAS.
  unfold is_true in HAS.
  decompose record HAS.
  unfold contains_single.
  intuition.
  assert (FEB:=amFindEmptyBound m (loop k) 99).
  rewrite FE in FEB.
  assert (FEC:=amFindEmptyCorrect m (loop k) 99).
  rewrite FE in FEC.
  assert (keys a z = k). {
    subst a.
    simpl.
    destruct (Z.eq_dec z z);tauto.
  }
  assert (keys a x = k). {
    subst a;simpl.
    destruct (Z.eq_dec x z);tauto.
  }
  assert (busybits a z = true). {
    subst a;simpl.
    destruct (Z.eq_dec z z);tauto.
  }
  assert (busybits a x = true). {
    subst a;simpl.
    destruct (Z.eq_dec x z);tauto.
  }
  pose (H5 x z).
  intuition.
  subst z.
  rewrite FEC in H0. discriminate H0.
Qed.

Lemma amPutContainsSingle: forall m k v, ~(full m) -> ~(contains m k) ->
                                         match amPut m k v with
                                           |Some map => contains_single map k
                                           |None => False
                                         end.
Proof.
  intros m k v NONFULL NOTHAS.
  assert (CONT:=amPutContains m k v NONFULL).
  rewrite (amCanPut m k v) in NONFULL.
  destruct (amPut m k v) eqn:PUT';[|tauto];unfold amPut in PUT'.
  destruct (find_empty m (loop k) 99) eqn: FE;[|symmetry in PUT';contradiction].
  injection PUT' as PUT;clear PUT'.
  unfold contains_single.
  split;[assumption|].
  intros.
  unfold contains in NOTHAS.
  subst a. simpl in *.
  destruct (Z.eq_dec x z).
  - destruct (Z.eq_dec y z).
    + omega.
    + apply not_ex_all_not with (n:=y) in NOTHAS.
      contradiction NOTHAS;intuition.
  - apply not_ex_all_not with (n:=x) in NOTHAS.
    contradiction NOTHAS;intuition.
Qed.

Lemma amCanErase: forall m k, contains m k <-> amErase m k <> None.
Proof.
  split;intro.
  - unfold amErase.
    apply amContainsCanFindKey with (s:=(loop k)) in H.
    destruct (find_key m (loop k) k 99);[discriminate|tauto].
  - apply amContainsCanFindKey with (s:=(loop k)).
    unfold amErase in H.
    destruct (find_key m (loop k) k 99);[discriminate|tauto].
Qed.

Lemma amEraseErase: forall m k, contains_single m k ->
                                match amErase m k with
                                  |Some map => ~(contains map k)
                                  |None => False
                                end.
Proof.
  intros m k [CONT SINGLE].
  apply amCanErase in CONT.
  destruct (amErase m k) eqn:ERZ';[|tauto];unfold amErase in ERZ'.
  assert (FKBOUND:=amFindKeyBound m k (loop k) 99).
  assert (FKCORRECT:=amFindKeyCorrect m k (loop k) 99).
  destruct (find_key m (loop k) k 99) eqn:FK;[|symmetry in ERZ';contradiction].
  injection ERZ' as ERZ;clear ERZ'.
  unfold contains.
  apply all_not_not_ex; intro x.
  subst a; simpl in *.
  destruct (Z.eq_dec x z).
  intuition.
  contradict SINGLE.
  intuition.
Qed.

Lemma amEraseNonFull: forall m k, match amErase m k with
                                    |Some map => ~(full map)
                                    |None => True
                                  end.
Proof.
  intros.
  destruct (amErase m k) eqn: ERZ';[|tauto].
  unfold amErase in ERZ'.
  assert (BND:=amFindKeyBound m k (loop k) 99).
  destruct (find_key m (loop k) k 99) eqn:FK;[|discriminate ERZ'].
  injection ERZ' as ERZ;clear ERZ'.
  unfold full.
  apply ex_not_not_all.
  exists z.
  subst a;simpl.
  replace (loop z) with z;[|symmetry;apply loop_small;assumption].
  destruct (Z.eq_dec z z);intuition.
Qed.

Lemma amNotContainsFindKeyFail: forall m k, ~(contains m k) <->
                                            (find_key m (loop k) k 99) = None.
Proof.
  intros.
  split;intro.
  - assert (CORR:=amFindKeyCorrect m k (loop k) 99).
    assert (BND:=amFindKeyBound m k (loop k) 99).
    destruct (find_key m (loop k) k 99) eqn:FK;[|tauto].
    contradiction H.
    unfold contains.
    exists z.
    intuition.
  - contradict H.
    apply amContainsCanFindKey;assumption.
Qed.

Lemma amNotContainsNotGet: forall m k, ~(contains m k) <-> amGet m k = None.
Proof.
  intros.
  unfold amGet.
  rewrite amNotContainsFindKeyFail.
  split;intro.
  - rewrite H;tauto.
  - destruct (find_key m (loop k) k 99);[discriminate H|tauto].
Qed.

Lemma amNotContainsNotErase: forall m k, ~(contains m k) <->
                                         amErase m k = None.
Proof.
  intros.
  unfold amErase.
  rewrite amNotContainsFindKeyFail.
  split;intro.
  - rewrite H;tauto.
  - destruct (find_key m (loop k) k 99);[discriminate H|tauto].
Qed.

Lemma amEraseOther: forall m k1 k2, k1 <> k2 ->
                                    match amErase m k1 with
                                      |Some map => amGet map k2 = amGet m k2
                                      |None => True
                                    end.
Proof.
  intros m k1 k2 NEQ.
  destruct (amErase m k1) eqn:ERZ';[|tauto].
  unfold amErase in ERZ'.
  assert (CORR:=amFindKeyCorrect m k1 (loop k1) 99).
  destruct (find_key m (loop k1) k1 99);[|discriminate ERZ'].
  decompose [and] CORR.
  injection ERZ' as ERZ;clear ERZ'.
  unfold amGet.
  unfold find_key.
  assert (forall k, (busybits m k && (k2 =? keys m k)) =
                    (busybits a k && (k2 =? keys a k)))%bool. {
    intro.
    subst a; simpl.
    destruct (Z.eq_dec k z);[|tauto].
    subst k.
    subst k1.
    apply Z.eqb_neq in NEQ.
    rewrite Z.eqb_sym in NEQ.
    rewrite NEQ.
    rewrite Bool.andb_false_r;simpl.
    auto.
  }
  replace (fun k : Z => (busybits a k && (k2 =? keys a k))%bool)
  with (fun k : Z => (busybits m k && (k2 =? keys m k))%bool).
  - rewrite <- ERZ.
    tauto.
  - apply functional_extensionality;assumption.
Qed.

Lemma put_nodups: forall m k v, nodups m -> amGet m k = None ->
                                match amPut m k v with
                                  |Some map => nodups map
                                  |None => True
                                end.
Proof.
  intros m k v NODUPS GET.
  rewrite <- amNotContainsNotGet in GET.
  assert (FEC:=amFindEmptyCorrect m (loop k) 99).
  destruct (amPut m k v) eqn:PUT';[|tauto];unfold amPut in PUT'.
  destruct (find_empty m (loop k) 99) eqn: FE;[|discriminate PUT'].
  injection PUT' as PUT;clear PUT'.
  unfold nodups.
  subst a;simpl.
  intros.
  destruct (Z.eq_dec x z), (Z.eq_dec y z).
  - subst x y;tauto.
  - contradict GET.
    unfold contains.
    exists y.
    intuition.
  - contradict GET.
    unfold contains.
    exists x.
    intuition.
  - apply NODUPS;intuition.
Qed.

Lemma erase_nodups: forall m k, nodups m -> match amErase m k with
                                              |Some map => nodups map
                                              |None => True
                                            end.
Proof.
  intros m k NODUPS.
  destruct (amErase m k) eqn:RZ';[|tauto];unfold amErase in RZ'.
  destruct (find_key m (loop k) k 99) eqn: FE;[|discriminate RZ'].
  injection RZ' as RZ;clear RZ'.
  unfold nodups;subst a; simpl.
  intros.
  destruct (Z.eq_dec x z), (Z.eq_dec y z).
  - subst x y;tauto.
  - discriminate.
  - discriminate.
  - apply NODUPS;intuition.
Qed.

Lemma get_put1: forall m k v, amGet m k = None ->
                              match amPut m k v with
                                |Some map => amGet map k = Some v
                                |None => True
                              end.
Proof.
  intros m k v GET.
  destruct (amPut m k v) eqn:PUT';[|tauto].
  assert (amPut m k v <> None) as NONFULL by
                                   (rewrite PUT';discriminate).
  rewrite <- amCanPut in NONFULL.
  apply amGetPut1 with (k:=k) (v:=v) in NONFULL.
  - rewrite PUT' in NONFULL.
    assumption.
  - apply amNotContainsNotGet;assumption.
Qed.  

Lemma get_put2: forall m k1 k2 v, k1 <> k2 ->
                                  match amPut m k1 v with
                                    |Some map => amGet map k2 = amGet m k2
                                    |None => True
                                  end.
Proof.
  intros m k1 k2 v NEQ.
  destruct (amPut m k1 v) eqn:PUT';[|tauto].
  assert (amPut m k1 v <> None) as NONFULL by
                                   (rewrite PUT';discriminate).
  rewrite <- amCanPut in NONFULL.
  apply amGetPut2 with m k1 k2 v in NONFULL.
  - rewrite PUT' in NONFULL.
    assumption.
  - assumption.
Qed.

Lemma  get_erase1: forall m k, amGet m k <> None -> nodups m ->
                               match amErase m k with
                                 |Some map => amGet map k = None
                                 |None => False
                               end.
Proof.
  intros m k HAS NODUPS.
  assert (contains_single m k) as HAS1.
  { unfold contains_single.
    split.
    - apply amCanGet;assumption.
    - intros.
      unfold nodups in NODUPS.
      apply NODUPS;intuition.
  }
  apply amEraseErase in HAS1.
  destruct (amErase m k).
  - apply amNotContainsNotGet;assumption.
  - assumption.
Qed.

Lemma get_erase2: forall m k1 k2, k1 <> k2 ->
                                  match amErase m k1 with
                                    |Some map => amGet map k2 = amGet m k2
                                    |None => True
                                  end.
Proof.
  apply amEraseOther.
Qed.

Lemma fullpsize: forall m i, (i <= 100)%nat -> full m -> (amPartSize m i = i)%nat.
Proof.
  intros m i BND FULL.
  induction i;unfold amPartSize.
  - auto.
  - fold amPartSize.
    rewrite IHi;[|omega].
    unfold full in FULL.
    replace (Z.of_nat i) with (loop (Z.of_nat i));[|apply loop_small;omega].

    specialize FULL with (Z.of_nat i).
    unfold is_true in FULL.
    rewrite FULL.
    omega.
Qed.

Lemma psize_less_linear: forall m i, (amPartSize m i <= i)%nat.
Proof.
  intros m i.
  induction i;unfold amPartSize;fold amPartSize.
  - auto.
  - destruct (busybits m (Z.of_nat i));omega.
Qed.

Lemma psize_less_linear_inc: forall m i1 i2, (amPartSize m i1 < i1)%nat ->
                                            (amPartSize m (i1 + i2) < (i1 + i2))%nat.
Proof.
  intros.
  induction i2.
  - replace (i1 + 0)%nat with i1;omega.
  - replace (i1 + S i2)%nat with (S (i1 + i2))%nat;[|omega].
    unfold amPartSize;fold amPartSize.
    destruct (busybits m (Z.of_nat (i1 + i2))).
    + omega.
    + omega.
Qed.

Lemma psize_non_full: forall m, ~full m -> exists i, (amPartSize m i < i /\
                                                     i <= 100)%nat.
Proof.
  intros m NONFULL.
  unfold full in NONFULL.
  unfold is_true in NONFULL.
  apply not_all_ex_not in NONFULL.
  decompose record NONFULL.
  exists (S (Z.to_nat (loop x))).
  assert (BOUNDZ:=(Loop_bound x)).
  split.
  - destruct (Z.to_nat (loop x)) eqn:Heqx.
    + unfold amPartSize.
      replace (loop x) with 0 in H.
      simpl; destruct (busybits m 0);[tauto|omega].
      SearchAbout BinInt.Z.to_nat.
      apply Z2Nat.inj;[omega|omega|].
      rewrite Heqx;auto.
    + unfold amPartSize;fold amPartSize.
      rewrite <- Heqx.
      rewrite Z2Nat.id;[|omega].
      destruct (busybits m (loop x)).
      * tauto.
      * assert (SLL:=psize_less_linear m n).
        destruct (busybits m (Z.of_nat n));omega.
  - assert (Z.to_nat (loop x) < 100)%nat.
    {
      replace 100%nat with (Z.to_nat 100);[|auto].
      rewrite <- Z2Nat.inj_lt;omega.
    }
    omega.
Qed.

Lemma psize_non_full_100: forall m, ~full m -> (amPartSize m 100 < 100)%nat.
Proof.
  intros.
  apply psize_non_full in H.
  decompose record H.
  pose (y:= 100 - (Z.of_nat x)).
  pose (i:= Z.to_nat y).
  assert (100 = x + i)%nat as CENT.
  {
    subst i y.
    rewrite <- Nat2Z.id with x.
    replace 100%nat with (Z.to_nat 100);[|auto].
    rewrite <- Z2Nat.inj_add.
    - rewrite Nat2Z.id.
      apply f_equal.
      omega.
    - omega.
    - rewrite Nat2Z.id.
      omega.
  }
  rewrite CENT.
  apply psize_less_linear_inc.
  assumption.
Qed.

Lemma psizefull: forall m, (forall i, i <= 100 -> amPartSize m i = i)%nat -> full m.
Proof.
  intros.
  apply NNPP.
  contradict H.
  apply psize_non_full in H.
  decompose record H.
  intro SIZEID.
  specialize SIZEID with x.
  intuition.
Qed.

Lemma psize100full: forall m, (amPartSize m 100 = 100)%nat -> full m.
Proof.
  intros.
  intros.
  apply NNPP.
  contradict H.
  apply psize_non_full_100 in H.
  omega.
Qed.  

Lemma full_psize_100: forall m, full m <-> (amPartSize m 100 = 100)%nat.
Proof.
  split;intro.
  - apply fullpsize;[omega|assumption].
  - apply psize100full;assumption.
Qed.

Lemma psize_not_care: forall m1 m2 i,
                       (forall j, 0 <= j < i ->
                                  busybits m1 (Z.of_nat j) = 
                                  busybits m2 (Z.of_nat j))%nat ->
                       amPartSize m1 i = amPartSize m2 i.
Proof.
  intros.
  induction i.
  - auto.
  - unfold amPartSize;fold amPartSize.
    replace (busybits m2 (Z.of_nat i))
    with (busybits m1 (Z.of_nat i));[|intuition].
    replace (amPartSize m2 i)
    with (amPartSize m1 i);[|apply IHi;intuition].
    tauto.
Qed.

Lemma psize_not_care_above:
  forall m1 m2 i, (i <= 100)%nat ->
    (forall j, i <= j <= 100 ->
               busybits m1 (Z.of_nat j) =
               busybits m2 (Z.of_nat j))%nat ->
    (amPartSize m1 100 + amPartSize m2 i =
     amPartSize m2 100 + amPartSize m1 i)%nat.
Proof.
  intros m1 m2 i BND J.
  pose (y := (100 - i)%nat).
  assert (i + y <= 100)%nat by (subst y;omega).
  replace 100%nat with (i + y)%nat;[|subst y;omega].
  induction y.
  - replace (i + 0)%nat with i;omega.
  - replace (i + S y)%nat with (S (i + y));[|omega].
    unfold amPartSize;fold amPartSize.
    replace (busybits m2 (Z.of_nat (i + y)))
    with (busybits m1 (Z.of_nat (i + y)));[|apply J;omega].
    destruct (busybits m1 (Z.of_nat (i + y)));lia.
Qed.

Lemma Z_lt_nat_le_100: forall z, 0 <= z < 100 -> (S (Z.to_nat z) <= 100)%nat.
Proof.
  intros.
  apply gt_le_S;red.
  rewrite Nat2Z.inj_lt.
  rewrite Z2Nat.id;simpl;omega.
Qed.  

Lemma z_to_nat_and_back:forall z j, 0 <= z < 100 ->
                                    (S (Z.to_nat z) <= j <= 100)%nat ->
                                    z < (Z.of_nat j).
Proof.
  intros.
  rewrite Z2Nat.inj_lt;[|omega|omega].
  rewrite Nat2Z.id.
  apply lt_S_n.
  omega.
Qed.

Lemma psize_put: forall m k v, match amPut m k v with
                                    |Some map =>
                                     amPartSize map 100 = S (amPartSize m 100)
                                    |None => True
                                  end.
Proof.
  intros.
  destruct (amPut m k v) eqn:PUT';[|tauto];unfold amPut in PUT'.
  assert (FEB:=amFindEmptyBound m (loop k) 99).
  assert (FEC:=amFindEmptyCorrect m (loop k) 99).
  destruct (find_empty m (loop k) 99) eqn: FE;[|discriminate PUT'].
  injection PUT' as PUT;clear PUT'.
  pose (x:=(S (Z.to_nat z))).
  assert (amPartSize a 100 + amPartSize m x =
          amPartSize m 100 + amPartSize a x)%nat.
  {
    apply psize_not_care_above.
    - subst x; apply Z_lt_nat_le_100;assumption.
    - intros.
      subst a;simpl.
      destruct (Z.eq_dec (Z.of_nat j) z).
      + apply z_to_nat_and_back with z j in FEB;[omega|assumption].
      + tauto.
  }
  replace (amPartSize a x) with (S (amPartSize m x)) in H.
  - omega.
  - subst x.
    unfold amPartSize; fold amPartSize.
    replace (amPartSize a (Z.to_nat z))
    with (amPartSize m (Z.to_nat z)).
    + subst a;simpl.
      rewrite Z2Nat.id;[|omega].
      rewrite FEC.
      destruct (Z.eq_dec z z);[omega|tauto].
    + apply psize_not_care.
      intros.
      subst a;simpl.
      destruct (Z.eq_dec (Z.of_nat j) z).
      * assert (j = Z.to_nat z) by (subst z; rewrite Nat2Z.id;tauto).
        omega.
      * tauto.
Qed.

Lemma psize_erase: forall m k, match amErase m k with
                                |Some map =>
                                 S (amPartSize map 100) = amPartSize m 100
                                |None => True
                              end.
Proof.
  intros.
  destruct (amErase m k) eqn:EZ';[|tauto];unfold amErase in EZ'.
  assert (FKB:=amFindKeyBound m k (loop k) 99).
  assert (FKC:=amFindKeyCorrect m k (loop k) 99).
  destruct (find_key m (loop k) k 99) eqn: FK;[|discriminate EZ'].
  injection EZ' as EZ;clear EZ'.
  pose (x:=(S (Z.to_nat z))).
  assert (amPartSize a 100 + amPartSize m x =
          amPartSize m 100 + amPartSize a x)%nat.
  {
    apply psize_not_care_above.
    - subst x; apply Z_lt_nat_le_100;assumption.
    - intros.
      subst a;simpl.
      destruct (Z.eq_dec (Z.of_nat j) z).
      + apply z_to_nat_and_back with z j in FKB;[omega|assumption].
      + tauto.
  }
  replace (amPartSize m x) with (S (amPartSize a x)) in H.
  - omega.
  - subst x.
    unfold amPartSize; fold amPartSize.
    replace (amPartSize a (Z.to_nat z))
    with (amPartSize m (Z.to_nat z)).
    + subst a;simpl.
      rewrite Z2Nat.id;[|omega].
      unfold is_true in FKC;decompose record FKC.
      rewrite H0.
      destruct (Z.eq_dec z z);[omega|tauto].
    + apply psize_not_care.
      intros.
      subst a;simpl.
      destruct (Z.eq_dec (Z.of_nat j) z).
      * assert (j = Z.to_nat z) by (subst z; rewrite Nat2Z.id;tauto).
        omega.
      * tauto.
Qed.


Lemma full_size: forall m, full m <-> (amSize m = 100)%nat.
Proof.
  unfold amSize;apply full_psize_100.
Qed.

Lemma non_full_size: forall m, ~ full m <-> (amSize m < 100)%nat.
Proof.
  split;intro.
  - apply psize_non_full_100;assumption.
  - contradict H.
    apply full_size in H.
    omega.
Qed.    

Lemma size_put: forall m k v, match amPut m k v with
                                    |Some map =>
                                     amSize map = S (amSize m)
                                    |None => True
                                  end.
Proof.
  unfold amSize; apply psize_put.
Qed.

Lemma size_erase: forall m k, match amErase m k with
                                |Some map =>
                                 S (amSize map) = amSize m
                                |None => True
                              end.
Proof.
  unfold amSize; apply psize_erase.
Qed.
