Require Import floyd.proofauto.
Require Import assoc.
Require Import assoc_spec.
Require Import Coq.Logic.FunctionalExtensionality.

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
    WITH sh : share, k : Z, arr : ArrayZ, vk : val, varr : val
    PRE [_arr OF (tptr tint), _key OF tint]
        PROP (0 <= k < 100; repr k vk)
        LOCAL (`(eq vk) (eval_id _key);
               `(eq varr) (eval_id _arr);
               `isptr (eval_id _arr))
        SEP (`(array_at tint sh (fun x => (Vint (Int.repr (arrGet arr x))))
                        0 100) (eval_id _arr))
    POST [tint] `(array_at tint sh (fun x => (Vint (Int.repr (arrGet arr x))))
                           0 100 varr) &&
                 local(`(eq (Vint (Int.repr (arrGet arr k)))) retval).

Definition set_spec :=
  DECLARE _set
     WITH sh : share, k : Z, v : Z, arr : ArrayZ, vk : val, vv : val, varr : val
     PRE [_arr OF (tptr tint), _key OF tint, _val OF tint]
         PROP (0 <= k < 100; writable_share sh; repr k vk; repr v vv)
         LOCAL (`(eq vk) (eval_id _key);
                `(eq vv) (eval_id _val);
                `(eq varr) (eval_id _arr);
                `isptr (eval_id _arr))
         SEP (`(array_at tint sh (fun x => (Vint (Int.repr (arrGet arr x))))
                         0 100)
                         (eval_id _arr))
     POST [tvoid] `(array_at tint sh 
                             (fun x => (Vint (Int.repr (arrGet (arrPut arr k v) x))))
                             0 100 varr).

Definition c_get_spec :=
  DECLARE _cGet
    WITH sh : share, k : Z, arr : CircleArrayZ, vk : val, varr : val
    PRE [_arr OF (tptr tint), _key OF tint]
        PROP (repr k vk)
        LOCAL (`(eq vk) (eval_id _key);
               `(eq varr) (eval_id _arr);
               `isptr (eval_id _arr))
        SEP (`(array_at tint sh (fun x => (Vint (Int.repr (caGet arr x))))
                        0 100) (eval_id _arr))
    POST [tint] `(array_at tint sh (fun x => (Vint (Int.repr (caGet arr x))))
                           0 100 varr) &&
                 local(`(eq (Vint (Int.repr (caGet arr k)))) retval).

Definition c_set_spec :=
  DECLARE _cSet
     WITH sh : share, k : Z, v : Z, arr : CircleArrayZ, vk : val, vv : val, varr : val
     PRE [_arr OF (tptr tint), _key OF tint, _val OF tint]
         PROP (writable_share sh; Int.min_signed <= k <= Int.max_signed;
               repr k vk; Int.min_signed <= v <= Int.max_signed; repr v vv)
         LOCAL (`(eq vk) (eval_id _key);
                `(eq vv) (eval_id _val);
                `(eq varr) (eval_id _arr);
                `isptr (eval_id _arr))
         SEP (`(array_at tint sh (fun x => (Vint (Int.repr (caGet arr x))))
                         0 100)
                         (eval_id _arr))
     POST [tvoid] `(array_at tint sh 
                             (fun x => (Vint (Int.repr (caGet (caPut arr k v) x))))
                             0 100 varr).

Definition Vprog : varspecs := nil.
Definition Gprog : funspecs := get_spec :: set_spec :: c_get_spec :: c_set_spec :: nil.

Lemma body_c_get: semax_body Vprog Gprog f_cGet c_get_spec.
Proof.
  start_function.
  name karg _key.
  name arrarg _arr.
  name rezloc _rez.
  forward_call (sh,(Zmod k 100),arr,(Vint (Int.repr (Zmod k 100))), varr).
  entailer!.
  simpl.
  
  unfold Int.mone.
  
  SearchAbout Int.eq.
  
  assert (Int.eq (Int.repr 100) (Int.repr (-1)) = false).
  apply Int.eq_false.
  unfold Int.repr.
  simpl.
  admit.

  rewrite H2.
  rewrite andb_false_r.
  simpl.
  auto.
  apply Z_mod_lt; omega.
  apply Z_mod_lt; omega.
  apply mk_repr.
  apply Z.le_ge.
  apply Z_mod_lt; omega.
  unfold Int.modulus.
  unfold two_power_nat, Int.wordsize.
  unfold Wordsize_32.wordsize, shift_nat.
  unfold nat_iter.

  assert (forall a b c, a < b -> b < c -> a < c) as Lt_Lt_trans by admit.
  apply Lt_Lt_trans with 100.
  apply Z_mod_lt; omega.
  omega.
  rewrite H1 in H.
  assert (karg = (Int.repr k)).
  inv H.
  tauto.
  rewrite H2.
  unfold sem_mod.
  unfold sem_binarith.
  unfold classify_binarith.
  unfold tint.
  unfold both_int.
  unfold sem_cast.
  unfold classify_cast.
  unfold binarith_type.
  unfold sem_cast_neutral.
  simpl.
  unfold Int.mone.
  assert (Int.eq (Int.repr 100) (Int.repr (-1)) = false) by admit.
  rewrite H3.
  rewrite andb_false_r.
  unfold force_val.
  
  unfold Int.mods.
  rewrite Int.signed_repr.
  rewrite Int.signed_repr.
  repeat apply f_equal.
  destruct k.
  auto.
  rewrite Zquot.Zrem_Zmod_pos;auto.
  admit.
  omega.
  unfold Z.rem.
  unfold Z.quotrem.
  unfold Zmod.
  admit.
  unfold Int.min_signed, Int.max_signed, Int.half_modulus, Int.modulus, two_power_nat, Int.wordsize, Wordsize_32.wordsize, shift_nat, nat_iter.
  simpl.
  omega.
  admit.
  after_call.
  forward.
Qed.

Lemma body_c_set: semax_body Vprog Gprog f_cSet c_set_spec.
Proof.
  start_function.
  name karg _key.
  name arrarg _arr.
  name valarg _val.
  forward_call (sh, (Zmod k 100), v, arr, (Vint (Int.repr (Zmod k 100))), vv, varr).
  entailer!.
  admit.
  apply Z_mod_lt; omega.
  apply Z_mod_lt; omega.
  admit.
  rewrite <- H6. assumption.
  admit.
  after_call.
  forward.
Qed.

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
    simpl.
    auto.
  - forward.
    entailer!.
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
  rename H1 into RK.
  rename H2 into RV.
  rename H3 into PARR.

  instantiate (1:=vv).
  instantiate (2:=k).

  assert (offset_val (Int.repr (sizeof tint * k)) (eval_id _arr rho) =
          force_val (sem_add_pi tint (eval_id _arr rho) (eval_id _key rho))).
  inversion RK.
  rewrite sem_add_pi_ptr.
  unfold force_val.
  apply f_equal2.
  rewrite mul_repr.
  auto.
  auto.
  assumption.

  assert (eval_id _val rho = force_val (sem_cast_neutral (eval_id _val rho))).
  inversion RV.
  simpl.
  tauto.
  entailer.
  rename H1 into RK.
  rename H2 into RV.
  forward.
  
  assert ((upd (fun x : Z => Vint (Int.repr (arrGet arr x))) k (Vint valarg)) = 
          (fun x : Z => Vint (Int.repr (arrGet (arrPut arr k v) x)))) as ARR_PUT.
  unfold upd.
  apply functional_extensionality.
  intro.
  unfold eq_dec.
  unfold initial_world.EqDec_Z.
  unfold zeq.
  elim (Z.eq_dec k x).
  - intro HEQ.
    rewrite HEQ.
    rewrite getput1.
    inversion RV.
    tauto.
  - intro HNEQ.
    rewrite getput2.
    tauto.
    assumption.
  - rewrite ARR_PUT.
    entailer.
Qed.

Existing Instance NullExtension.Espec.


Theorem all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_skipn.
semax_func_cons body_get.
semax_func_cons body_set.
semax_func_cons body_c_get.
semax_func_cons body_c_set.
apply semax_func_nil.
Qed.

