Require Import floyd.proofauto.
Require Import assoc.
Require Import assoc_spec.

Local Open Scope logic.
Local Open Scope Z.


Definition get_spec :=
  DECLARE _get
    WITH sh : share, k : Z, arr : Z->val, vk : val, varr : val
    PRE [_key OF tint, _arr OF (tptr tint)]
        PROP (0 <= k < 100; forall i, 0 <= i < 100 -> is_int (arr i))
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
  forward.
  entailer!.
  admit.
  admit.
  admit.
Qed.

Lemma body_set: semax_body Vprog Gprog f_set set_spec.
Proof.
  start_function.
  name karg _key.
  name valarg _val.
  name arrarg _arr.
  admit.
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

