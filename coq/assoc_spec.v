Require Import Coq.ZArith.Zbool.
Require Import Coq.ZArith.BinInt.
Require Import ZArith.ZArith_dec.
Require Import ZArith.ZArith_base.
Require Import ZArith.Zdiv.
Require Import Coq.Setoids.Setoid.

Local Open Scope Z.

Definition ArrayZ := Z->Z.

Function arrPut (arr: ArrayZ) (k:Z) (v:Z) : ArrayZ :=
  fun (kk:Z) => if (Z.eq_dec k kk) then v else arr kk.

Function arrGet (arr: ArrayZ) (k:Z) : Z :=
  arr k.

Lemma getput1: forall arr k v, arrGet (arrPut arr k v) k = v.
Proof.
intros.
unfold arrGet, arrPut.
destruct Z.eq_dec;[auto|tauto].
Qed.

Lemma getput2: forall arr k1 k2 v2, k2 <> k1 -> arrGet (arrPut arr k2 v2) k1 = 
                                                arrGet arr k1.
Proof.
intros.
unfold arrGet, arrPut.
destruct Z.eq_dec;[contradiction|tauto].
Qed.

Definition CircleArrayZ := ArrayZ.

Function hash (k:Z): Z :=
  if (Z.ltb k 0) then (Z.rem k 100) + 99 else (Z.rem k 100).

Function caPut (arr: CircleArrayZ) (k:Z) (v:Z) : CircleArrayZ :=
  arrPut arr (hash k) v.

Function caGet (arr:CircleArrayZ) (k:Z) : Z :=
  arrGet arr (hash k).

Lemma Cgetput1: forall arr k v, caGet (caPut arr k v) k = v.
Proof.
intros.
unfold caGet, caPut.
apply getput1.
Qed.

Lemma Cgetput2: forall arr k1 k2 v2, hash k2 <> hash k1 -> 
                                     caGet (caPut arr k2 v2) k1 =
                                     caGet arr k1.
Proof.
intros.
unfold caGet, caPut.
apply getput2.
assumption.
Qed.

Lemma caPut_is: forall arr k v, caPut arr k v = arrPut arr (hash k) v.
Proof.
  unfold caPut; auto.
Qed.

Lemma caGet_is: forall arr k, caGet arr k = arrGet arr (hash k).
Proof.
  unfold caGet; auto.
Qed.

Lemma Zero_le_hash: forall k, 0 <= hash k.
Proof.
  intro.
  unfold hash.
  destruct k;simpl.
  - apply Z.rem_nonneg; omega.
  - apply Z.rem_nonneg.
    omega.
    pose (Zgt_pos_0 p); omega.
  - assert (Z.rem (Z.neg p) 100 <= 0) as NONPOS.
    apply Z.rem_nonpos.
    omega.
    pose (Zlt_neg_0 p); omega.

    assert (-100 < Z.rem (Z.neg p) 100).
    assert (Z.abs (Z.rem (Z.neg p) 100) < Z.abs 100)
      as BOUND by
          (apply Z.rem_bound_abs; omega).

    apply Z.abs_lt in BOUND.
    simpl in BOUND.
    omega.
    omega.
Qed.

Lemma hash_lt_100: forall k, hash k < 100.
Proof.
  intro.
  unfold hash.
  destruct k;simpl.
  - apply Z.rem_bound_pos.
    omega.
    omega.
  - apply Z.rem_bound_pos.
    pose (Zgt_pos_0 p); omega.
    omega.
  - assert (100 = 1 + 99) as P0 by omega.
    rewrite P0 at 2.
    apply Zplus_lt_compat_r.
    Check Z.rem_nonpos.
    SearchAbout Z.rem.
    Eval compute in (Z.rem (-100) 100).
    assert (Z.rem (Z.neg p) 100 <= 0) as NONPOS.
    apply Z.rem_nonpos.
    omega.
    pose (Zlt_neg_0 p); omega.
    omega.
Qed.    
