Require Import floyd.proofauto.
Require Import assoc.
Require Import assoc_spec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Psatz.

Local Open Scope logic.
Local Open Scope Z.

(* Auxillary definitions *)
Inductive repr : Z -> val -> Prop :=
| mk_repr : forall z, Int.min_signed <= z <= Int.max_signed -> repr z (Vint (Int.repr z)).

(* Function specifications *)
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

Definition hash_spec :=
  DECLARE _hash
    WITH sh : share, k : Z, vk : val
    PRE [_key OF tint]
        PROP ( repr k vk)
        LOCAL (`(eq vk) (eval_id _key))
        SEP ()
    POST [tint] local(`(eq (Vint (Int.repr (hash k)))) retval).

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
         PROP (writable_share sh; repr k vk; repr v vv)
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
Definition Gprog : funspecs := get_spec :: set_spec :: hash_spec
                                        :: c_get_spec :: c_set_spec :: nil.

(* Auxillary lemmas *)

(*
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
*)

Lemma k_from_val: forall (k:Z) (karg : int), repr k (Vint karg) -> 0 <= k < 100 ->
                                             Int.signed karg = k.
Proof.
intros.
inversion H.
apply Int.signed_repr.
assumption.
Qed.

Lemma f_notequal: forall (A B : Type) (f : A -> B) (x y : A), ~ f x = f y -> ~ x = y.
Proof.
  pose proof f_equal as FEQ.
  assert (forall A B:Prop, (A -> B) -> (~B -> ~A)) as CONTRAPOSITION by tauto.
  intros A B f x y.
  apply CONTRAPOSITION.
  apply FEQ.
Qed.

Lemma neq_100_mone: (Int.eq (Int.repr 100) Int.mone = false).
Proof.
  apply Int.eq_false.
  apply f_notequal with Z Int.intval.
  simpl.
  omega.
Qed.

Lemma neq_100_zero: (Int.eq (Int.repr 100) Int.zero = false).
Proof.
  apply Int.eq_false.
  apply f_notequal with Z Int.intval.
  simpl.
  omega.
Qed.

Lemma hash_bound: forall k, Int.min_signed <= hash k <= Int.max_signed.
Proof.
  intro.
  unfold Int.min_signed, Int.max_signed, Int.half_modulus, Int.modulus, two_power_nat, Int.wordsize, Wordsize_32.wordsize, shift_nat, nat_iter;simpl.
  split.
  pose (Zero_le_hash k).
  omega.
  pose (hash_lt_100 k).
  omega.
Qed.

Lemma Zmod_less: forall a b c, b > 0 -> b <= c -> a mod b < c.
Proof.
  intros.
  assert (forall a b c, a < b -> b <= c -> a < c) as lt_le_trans by (intros; lia).
  apply lt_le_trans with b.
  apply Z_mod_lt;auto.
  assumption.
Qed.

Lemma body_hash: semax_body Vprog Gprog f_hash hash_spec.
Proof.
  start_function.
  name karg _key.
  forward_if (PROP (Int.min_signed <= k <= Int.max_signed; repr k vk;
                    0 <= k)
                   LOCAL (`(eq vk) (eval_id _key)) SEP()).
  - forward. rename H into REPRK. rename H0 into KLT0.
    entailer!.
    + rewrite neq_100_mone.
      rewrite andb_false_r.
      simpl; auto.
      
    + unfold force_val, sem_mod, sem_add_default, sem_cast_neutral, sem_binarith.
      simpl.
      unfold both_int, sem_cast_neutral.
      simpl.
      rewrite neq_100_mone.
      rewrite andb_false_r.
      unfold is_int.
      auto.

    + assert (karg = (Int.repr k)) as KARGEQK by (inv REPRK;tauto).
      rewrite KARGEQK.
      unfold force_val, sem_mod, sem_add_default, sem_cast_neutral.
      unfold sem_binarith, both_int, sem_cast_neutral.
      simpl.
      rewrite neq_100_mone.
      rewrite andb_false_r.
      simpl.
      apply f_equal.
      unfold Int.mods.
      repeat rewrite Int.signed_repr.
      rewrite add_repr.
      apply f_equal.
      unfold hash.
      assert (k < 0) as KLESS0.
      rewrite KARGEQK in KLT0.
      unfold Int.lt in KLT0.
      rewrite Int.signed_repr in KLT0.
      rewrite Int.signed_repr in KLT0.
      destruct (zlt k 0).
      assumption.
      discriminate KLT0.
      unfold Int.min_signed, Int.max_signed, Int.half_modulus, Int.modulus, two_power_nat, Int.wordsize, Wordsize_32.wordsize, shift_nat, nat_iter.      
      split;simpl;omega.
      inv REPRK.
      assumption.
      assert ((k <? 0) = true).
      unfold "<?".
      unfold "?=".
      destruct k; [omega|pose (Zgt_pos_0 p);omega|tauto].
      rewrite H.
      tauto.
      unfold Int.min_signed, Int.max_signed, Int.half_modulus, Int.modulus, two_power_nat, Int.wordsize, Wordsize_32.wordsize, shift_nat, nat_iter.
      split;simpl;omega.
      inv REPRK;assumption.
  - forward.
    entailer. rename H into REPRK.
    inv REPRK. entailer.
  - forward.
    entailer!.
    + rewrite neq_100_mone.
      rewrite andb_false_r.
      simpl.
      auto.
    + unfold force_val, sem_mod, sem_add_default, sem_cast_neutral, sem_binarith.
      simpl.
      unfold both_int, sem_cast_neutral.
      simpl.
      rewrite neq_100_mone.
      rewrite andb_false_r.
      unfold is_int.
      auto.
    + unfold force_val, sem_mod, sem_add_default, sem_cast_neutral.
      unfold sem_binarith, both_int, sem_cast_neutral.
      simpl.
      rewrite neq_100_mone.
      rewrite andb_false_r.
      apply f_equal.
      unfold Int.mods.
      repeat rewrite Int.signed_repr.
      apply f_equal.
      inv H.
      rewrite Int.signed_repr.
      unfold hash.
      assert ((k <? 0) = false).
      unfold "<?", "?=".
      destruct k;[tauto|tauto|pose (Zlt_neg_0 p); omega].
      rewrite H.
      tauto.
      split;assumption.
      unfold Int.min_signed, Int.max_signed, Int.half_modulus, Int.modulus, two_power_nat, Int.wordsize, Wordsize_32.wordsize, shift_nat, nat_iter.
      split;simpl;omega.
Qed.

Lemma body_c_get: semax_body Vprog Gprog f_cGet c_get_spec.
Proof.
  start_function.
  name karg _key.
  name arrarg _arr.
  name rezloc _rez.
  name hloc _h.
  forward_call (sh,k,vk). (* hash(key) *)
  entailer!.
  rewrite <- H1; assumption.
  

  admit.
  after_call.
  forward_call (sh,(hash k),arr,(Vint (Int.repr (hash k))), varr).
  entailer!. (* get(arr, h) *)
  - apply Zero_le_hash.
  - apply hash_lt_100.
  - apply mk_repr.
    apply hash_bound.
  -

  unfold sem_add_default, sem_mod, force_val.
simpl.  
  unfold sem_cast_neutral, both_int.
  rewrite neq_100_mone.
  rewrite neq_100_zero.
  simpl.
  rewrite andb_false_r.
  unfold denote_tc_nodivover.
  rewrite neq_100_mone.
  rewrite andb_false_r.
  simpl.
  auto.
  rewrite neq_100_mone.
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
  apply Zmod_less; omega.

  assert (Vint (Int.repr k) = Vint karg) as kEQkarg by (inv H;assumption).
  rewrite <- kEQkarg.
  unfold sem_mod.
  simpl. 
  unfold both_int.
  simpl.
  rewrite neq_100_mone.
  rewrite andb_false_r.
  unfold Int.mods.
  simpl.
  rewrite andb_false_r.
  unfold sem_cast_neutral, force_val.
  repeat apply f_equal.
  rewrite add_repr.
  repeat rewrite Int.signed_repr.
  apply Zmod_eq_pos_Zrem.

 unfold sem_binarith.
  unfold classify_binarith.
  unfold tint.
  unfold both_int.
  unfold sem_cast.
  unfold classify_cast.
  unfold binarith_type.
  unfold sem_cast_neutral.
  simpl.
  rewrite neq_100_mone.
  rewrite andb_false_r.
  unfold force_val.
  unfold Int.mods.
  rewrite Int.signed_repr.
  rewrite Int.signed_repr.
  repeat apply f_equal.

Eval compute in Z.rem (-5) 100.

  Print Z.modulo.
  Print Z.pos_div_eucl.
  Print Z.quotrem.


  destruct k.
  auto.
  rewrite Zquot.Zrem_Zmod_pos;auto.
  lia.
  omega.
  unfold Z.rem.
  unfold Z.quotrem.
  unfold Zmod.

Eval compute Z.div_eucl

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

