Require Import Coq.ZArith.Zbool.
Require Import Coq.ZArith.BinInt.
Require Import ZArith.ZArith_dec.
Require Import Coq.Setoids.Setoid.

Local Open Scope Z_scope.
(*Local Open Scope Z.*)
Locate Z.

Definition ArrayZ := Z->Z.

Function arrPut (arr: ArrayZ) (k:Z) (v:Z) : Z -> Z :=
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

