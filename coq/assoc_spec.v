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

Function caPut (arr: CircleArrayZ) (k:Z) (v:Z) : CircleArrayZ :=
  arrPut arr (Zmod k 100) v.

Function caGet (arr:CircleArrayZ) (k:Z) : Z :=
  arrGet arr (Zmod k 100).

Lemma Cgetput1: forall arr k v, caGet (caPut arr k v) k = v.
Proof.
intros.
unfold caGet, caPut.
apply getput1.
Qed.

Lemma Cgetput2: forall arr k1 k2 v2, k2 mod 100 <> k1 mod 100 -> 
                                     caGet (caPut arr k2 v2) k1 =
                                     caGet arr k1.
Proof.
intros.
unfold caGet, caPut.
apply getput2.
assumption.
Qed.

