Require Import floyd.proofauto.
Require Import assoc.
Require Import assoc_spec.

Local Open Scope logic.
Local Open Scope Z.

Inductive repr : Z -> val -> Prop :=
| mk_repr : forall z, z >= 0 -> z < Int.modulus -> repr z (Vint (Int.repr z)).

Lemma k_in_range: forall k : Z, 0 <= k < 100 -> Int.min_signed <= k <= Int.max_signed.
Proof.
  split.
  unfold Int.min_signed, Int.half_modulus, Int.modulus.
  unfold Int.wordsize, Wordsize_32.wordsize.
  unfold two_power_nat.
  unfold shift_nat.
  unfold nat_iter.
  simpl.
  omega.
  unfold Int.max_signed, Int.half_modulus, Int.modulus,
  Int.wordsize, Wordsize_32.wordsize,
  two_power_nat, shift_nat, nat_iter.
  simpl; omega.
Qed.


Lemma k_from_val: forall (k:Z) (karg : int), repr k (Vint karg) -> 0 <= k < 100 ->
                                             Int.signed karg = k.
Proof.
intros.
inversion H.
apply Int.signed_repr.
apply k_in_range.
assumption.
Qed.

Definition get_spec :=
  DECLARE _get
    WITH sh : share, k : Z, arr : Z->val, vk : val, varr : val
    PRE [_key OF tint, _rez OF tint, _arr OF (tptr tint)]
        PROP (0 <= k < 100; forall i, 0 <= i < 100 -> is_int (arr i);
              repr k vk)
        LOCAL (`(eq vk) (eval_id _key);
               `(eq varr) (eval_id _arr);
               `isptr (eval_id _arr))
        SEP (`(array_at tint sh arr
                        0 100) (eval_id _arr))
    POST [tint] `(array_at tint sh arr
                           0 100 varr) &&
                 local(`(eq (arr k)) retval).

Definition set_spec :=
  DECLARE _set
     WITH sh : share, k : Z, v : Z, arr : Z->Z, vk : val, vv : val, varr : val
     PRE [_key OF tint, _val OF tint, _arr OF (tptr tint)]
         PROP (0 <= k < 100; forall i, 0 <= i < 100 -> is_int (Vint (Int.repr (arrGet arr i)));
               writable_share sh)
         LOCAL (`(eq vk) (eval_id _key);
                `(eq vv) (eval_id _val);
                `(eq varr) (eval_id _arr);
                `isptr (eval_id _arr))
         SEP (`(array_at tint sh (fun x:Z => (Vint (Int.repr (arrGet arr x)))) 0 100)
                         (eval_id _arr))
     POST [tvoid] `(array_at tint sh (fun x:Z => (Vint (Int.repr (arrGet (arrPut arr k v) x))))
                             0 100 varr).

Definition Vprog : varspecs := nil.
Definition Gprog : funspecs := get_spec :: set_spec :: nil.

Lemma body_get: semax_body Vprog Gprog f_get get_spec.
Proof.
  start_function.
  name karg _key.
  name arrarg _arr.
  name rezloc _rez.
  forward.
  entailer!.
  - rewrite k_from_val with (k:=k) by assumption.
    omega.
  - rewrite k_from_val with (k:=k) by assumption.
    omega.
  - rewrite k_from_val with (k:=k) by assumption.
    apply H0.
    assumption.
  - forward.
    entailer!.
    rewrite <- H2.
    rewrite k_from_val with (k:=k) by assumption.
    tauto.
Qed.

Lemma body_set: semax_body Vprog Gprog f_set set_spec.
Proof.
  start_function.
  name karg _key.
  name valarg _val.
  name arrarg _arr.
  forward.



SearchAbout force_val.
  SearchAbout offset_val.
  SearchAbout add_ptr_int.
  Qed.




Existing Instance NullExtension.Espec.



Theorem all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_skipn.
pose proof body_get.
Check semax_func_cons.
Check mk_funspec.
apply semax_func_cons with (V:=Vprog) (G:=Gprog) (G':=set_spec::nil) (fs:=set_spec::nil)
                                      (id:=_get) (f:=f_get).
SearchAbout semax_func.
semax_func_cons body_get.
semax_func_cons body_set.
apply semax_func_nil.
Qed.

