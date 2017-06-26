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
        PROP (0 <= k < 100; repr k vk; isptr varr)
        LOCAL (`(eq vk) (eval_id _key);
               `(eq varr) (eval_id _arr))

        SEP (`(array_at tint sh (fun x => (Vint (Int.repr (arrGet arr x))))
                        0 100) (eval_id _arr))
    POST [tint] `(array_at tint sh (fun x => (Vint (Int.repr (arrGet arr x))))
                           0 100 varr) &&
                 local(`(eq (Vint (Int.repr (arrGet arr k)))) retval).

Definition set_spec :=
  DECLARE _set
     WITH sh : share, k : Z, v : Z, arr : ArrayZ, vk : val, vv : val, varr : val
     PRE [_arr OF (tptr tint), _key OF tint, _val OF tint]
         PROP (0 <= k < 100; writable_share sh; repr k vk; repr v vv;
              isptr varr)
         LOCAL (`(eq vk) (eval_id _key);
                `(eq vv) (eval_id _val);
                `(eq varr) (eval_id _arr))
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
    POST [tint] local(`(eq (Vint (Int.repr (hash k)))) retval) && emp.

Definition c_get_spec :=
  DECLARE _cGet
    WITH sh : share, k : Z, arr : CircleArrayZ, vk : val, varr : val
    PRE [_arr OF (tptr tint), _key OF tint]
        PROP (repr k vk; isptr varr)
        LOCAL (`(eq vk) (eval_id _key);
               `(eq varr) (eval_id _arr))
        SEP (`(array_at tint sh (fun x => (Vint (Int.repr (caGet arr x))))
                        0 100) (eval_id _arr))
    POST [tint] `(array_at tint sh (fun x => (Vint (Int.repr (caGet arr x))))
                           0 100 varr) &&
                 local(`(eq (Vint (Int.repr (caGet arr k)))) retval).

Definition c_set_spec :=
  DECLARE _cSet
     WITH sh : share, k : Z, v : Z, arr : CircleArrayZ, vk : val, vv : val, varr : val
     PRE [_arr OF (tptr tint), _key OF tint, _val OF tint]
         PROP (writable_share sh; repr k vk; repr v vv; isptr varr)
         LOCAL (`(eq vk) (eval_id _key);
                `(eq vv) (eval_id _val);
                `(eq varr) (eval_id _arr))
         SEP (`(array_at tint sh (fun x => (Vint (Int.repr (caGet arr x))))
                         0 100)
                         (eval_id _arr))
     POST [tvoid] `(array_at tint sh 
                             (fun x => (Vint (Int.repr (caGet (caPut arr k v) x))))
                             0 100 varr).

Definition Vprog : varspecs := nil.
Definition Gprog : funspecs := get_spec :: set_spec :: hash_spec
                                        :: c_get_spec :: c_set_spec :: nil.

(* Helper tactics *)

Ltac unfold_int_limits :=
  unfold Int.min_signed, Int.max_signed, Int.half_modulus,
         Int.modulus, two_power_nat, Int.wordsize, Wordsize_32.wordsize,
         shift_nat, nat_iter;
  simpl.

Ltac auto_logic :=
  repeat rewrite andb_false_r; repeat rewrite andb_false_l; simpl; auto.

Ltac unfold_to_bare_Z :=
  unfold force_val, sem_mod, sem_add_default, sem_cast_neutral, sem_binarith;
  simpl;
  unfold both_int, sem_cast_neutral;
  simpl;
  unfold Int.mods;
  repeat rewrite Int.signed_repr;
  try (unfold_int_limits; omega);
  repeat rewrite add_repr;
  repeat rewrite sem_add_pi_ptr;
  repeat unfold force_val;
  repeat rewrite mul_repr.

Ltac repr_bound k :=
  match goal with
    |[H:repr k _ |-Int.min_signed <= k <= Int.max_signed] => inv H; assumption
    |[H:repr k _ |-context[Int.min_signed <= k]] => inv H
    |[H:repr k _ |-context[k <= Int.max_signed]] => inv H
  end.

Ltac get_repr k :=
  repeat
    match goal with
      |[H:?a = (Int.repr k)|-context[Int.signed ?a]] =>
       rewrite H; rewrite Int.signed_repr;[|repr_bound k]
      |[H:?a = (Int.repr k)|-context[?a]] => rewrite H
      |[H:?a = (Vint (Int.repr k))|-context[?a]] => rewrite H; idtac "ololo"
      |[H:k = ?a|-context[?a]]=>rewrite <- H
      |[H:repr k (Vint ?a) |-context[?a]] =>
       let H' := fresh a "EQ" k in
       assert (a = (Int.repr k)) as H' by (inv H;tauto)
      |[H:repr k ?a |-context[?a]] =>
       let H' := fresh "EQ" k in
       assert (a = (Vint (Int.repr k))) as H' by (inv H; tauto)
    end.

(* Auxillary lemmas *)
Lemma klt0_is_false: forall k, 0 <= k -> (k <? 0) = false.
Proof.
  intro.
  unfold "<?", "?=".
  destruct k;[tauto|tauto|pose (Zlt_neg_0 p); omega].
Qed.

Lemma klt0_is_true: forall k, k < 0 -> (k <? 0) = true.
Proof.
  intro.
  unfold "<?".
  unfold "?=".
  destruct k; [omega|pose (Zgt_pos_0 p);omega|tauto].
Qed.

Lemma int_lt_to_zlt: forall a b, Int.lt (Int.repr a) (Int.repr b) = true ->
                                 Int.min_signed <= a <= Int.max_signed ->
                                 Int.min_signed <= b <= Int.max_signed -> a < b.
Proof.
  intros.
  unfold Int.lt in H.
  rewrite Int.signed_repr in H by assumption.
  rewrite Int.signed_repr in H by assumption.
  destruct (zlt a b).
  assumption.
  discriminate H.
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
  unfold_int_limits.
  split;[pose (Zero_le_hash k);omega | pose (hash_lt_100 k); omega].
Qed.

(* Proofs for spec-body correspondence *)
Lemma body_hash: semax_body Vprog Gprog f_hash hash_spec.
Proof.
  start_function.
  name karg _key.
  forward_if (PROP (Int.min_signed <= k <= Int.max_signed; repr k vk;
                    0 <= k)
                   LOCAL (`(eq vk) (eval_id _key)) SEP()).
  - forward; rename H0 into KLT0.
    entailer!.
    + rewrite neq_100_mone.
      auto_logic.
    + unfold_to_bare_Z.
      rewrite neq_100_mone.
      auto_logic.
    + get_repr k.
      unfold_to_bare_Z; [|repr_bound k].
      rewrite neq_100_mone.
      auto_logic.
      unfold_to_bare_Z.
      unfold hash.
      rewrite kargEQk in KLT0.
      apply int_lt_to_zlt in KLT0.
      rewrite klt0_is_true by assumption.
      tauto.
      repr_bound k.
      unfold_int_limits;split;omega.
  - forward.
    entailer.
    repr_bound k. entailer.
  - forward.
    entailer!.
    + rewrite neq_100_mone.
      auto_logic.
    + unfold_to_bare_Z.
      rewrite neq_100_mone.
      auto_logic.
    + unfold_to_bare_Z.
      rewrite neq_100_mone.
      auto_logic.
      get_repr k.
      unfold hash.
      rewrite klt0_is_false by assumption.
      tauto.
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
  get_repr vk; assumption.
  auto with closed.
  after_call.
  forward_call (sh,(hash k),arr,(Vint (Int.repr (hash k))), varr).
  entailer!. (* get(arr, h) *)
  - apply Zero_le_hash.
  - apply hash_lt_100.
  - constructor.
    apply hash_bound.
  - after_call.
    forward.
Qed.

Lemma body_c_set: semax_body Vprog Gprog f_cSet c_set_spec.
Proof.
  start_function.
  name karg _key.
  name arrarg _arr.
  name valarg _val.
  name hloc _h.
  forward_call (sh, k, vk). (* hash(key) *)
  entailer!.
  get_repr vk; assumption.
  after_call.
  forward_call (sh, (hash k), v, arr, (Vint (Int.repr (hash k))), vv, varr).
  entailer!.
  - apply Zero_le_hash.
  - apply hash_lt_100.
  - apply mk_repr.
    apply hash_bound.
  - get_repr vv; assumption.
  - after_call.
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
  - get_repr k; omega. 
  - get_repr k; omega.
  - get_repr k; simpl; auto.
  - forward.
    entailer!.
    get_repr k; trivial.
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

  entailer!.
  - get_repr k.
    unfold_to_bare_Z.
    auto.
    auto.
  - get_repr v.
    simpl.
    tauto.
  - forward.
    assert ((upd (fun x : Z => Vint (Int.repr (arrGet arr x))) k (Vint valarg)) = 
            (fun x : Z => Vint (Int.repr (arrGet (arrPut arr k v) x)))) as ARR_PUT.
    unfold upd.
    apply functional_extensionality.
    intro.
    unfold eq_dec, initial_world.EqDec_Z, zeq.
    elim (Z.eq_dec k x).
    + intro HEQ.
      rewrite HEQ.
      rewrite getput1.
      get_repr v.
      trivial.
    + intro HNEQ.
      rewrite getput2.
      tauto.
      assumption.
    + rewrite ARR_PUT.
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
semax_func_cons body_hash.
semax_func_cons body_c_get.
semax_func_cons body_c_set.
apply semax_func_nil.
Qed.

