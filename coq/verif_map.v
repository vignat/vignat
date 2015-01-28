Require Import floyd.proofauto.
Require Import map.
Require Import map_spec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Psatz.

Local Open Scope logic.
Local Open Scope Z.

(* Auxillary definitions *)
Inductive repr : Z -> val -> Prop :=
| mk_repr : forall z, Int.min_signed <= z <= Int.max_signed -> repr z (Vint (Int.repr z)).

Inductive Nrepr : nat -> val -> Prop :=
| mk_Nrepr : forall i:nat, (0 <= i <= Z.to_nat(Int.max_signed))%nat ->
                           Nrepr i (Vint (Int.repr (Z.of_nat i))).

(* Function specifications *)
Definition loop_spec :=
  DECLARE _loop
    WITH sh : share, k : Z, vk : val
    PRE [_k OF tint]
        PROP (repr k vk)
        LOCAL(`(eq vk) (eval_id _k))
        SEP ()
    POST [tint] local(`(eq (Vint (Int.repr (loop k)))) retval) && emp.

Definition find_empty_spec :=
  DECLARE _find_empty
    WITH sh : share, m : ArrMapZ, start : Z, i : nat,
         vbb : val, vstart : val, vi : val
    PRE [_busybits OF (tptr tint), _start OF tint, _i OF tint]
        PROP (0 <= start < 100;
              repr start vstart; Nrepr i vi; isptr vbb;
              (Z.of_nat i < 261905)(*my max recursion depth*))
        LOCAL (`(eq vstart) (eval_id _start);
               `(eq vi) (eval_id _i);
               `(eq vbb) (eval_id _busybits))
        SEP (`(array_at tint sh (fun x =>
                                   (Vint (Int.repr (if (busybits m x)
                                                    then 1
                                                    else 0))))
                        0 100) (eval_id _busybits))
    POST [tint]
         PROP()
         LOCAL (`(match (find_empty m start i) with
                    |Some x => (eq (Vint (Int.repr x)))
                    |None => (eq (Vint (Int.repr (-1))))
                  end) retval)
         SEP (`(array_at tint sh (fun x =>
                                    (Vint (Int.repr (if (busybits m x)
                                                     then 1
                                                     else 0))))
                         0 100 vbb)).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 ,
                  x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10
                  'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz)
                 (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) =>
                                  P%logic end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) =>
                                  Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0,
                           x4 at level 0, x5 at level 0, x6 at level 0,
                           x7 at level 0, x8 at level 0, x9 at level 0,
                           x10 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 ,
                  x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9
                  'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz)
                 (t1*t2*t3*t4*t5*t6*t7*t8*t9)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) =>
                                  P%logic end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) =>
                                  Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0,
                           x4 at level 0, x5 at level 0, x6 at level 0,
                           x7 at level 0, x8 at level 0, x9 at level 0,
                           P at level 100, Q at level 100).

Definition find_key_spec :=
  DECLARE _find_key
    WITH sh : share, m : ArrMapZ, start : Z, key : Z, i : nat,
         vbb : val, vkeys : val, vstart : val, vkey : val, vi : val
    PRE [_busybits OF (tptr tint), _keys OF (tptr tint),
         _start OF tint, _key OF tint, _i OF tint]
        PROP (0 <= start < 100;
              repr start vstart;
              repr key vkey; Nrepr i vi; isptr vbb; isptr vkeys;
              (Z.of_nat i < 261905);(*my max recursion depth*)
              (forall x, (Int.min_signed <= keys m x <= Int.max_signed)))
        LOCAL (`(eq vstart) (eval_id _start);
               `(eq vkey) (eval_id _key);
               `(eq vi) (eval_id _i);
               `(eq vbb) (eval_id _busybits);
               `(eq vkeys) (eval_id _keys))
        SEP (`(array_at tint sh (fun x =>
                                   (Vint (Int.repr (if (busybits m x)
                                                    then 1
                                                    else 0))))
                        0 100) (eval_id _busybits);
             `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                        0 100) (eval_id _keys))
    POST [tint]
         PROP()
         LOCAL (`(match (find_key m start key i) with
                    |Some x => (eq (Vint (Int.repr x)))
                    |None => (eq (Vint (Int.repr (-1))))
                  end) retval)
         SEP (`(array_at tint sh (fun x =>
                                    (Vint (Int.repr (if (busybits m x)
                                                     then 1
                                                     else 0))))
                         0 100 vbb);
              `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                         0 100 vkeys)).

Definition get_spec :=
  DECLARE _get
    WITH sh : share, m : ArrMapZ, key : Z,
         vbb : val, vkeys : val, vvals : val, vkey : val
    PRE [_busybits OF (tptr tint), _keys OF (tptr tint),
         _values OF (tptr tint), _key OF tint]
         PROP (repr key vkey; isptr vbb; isptr vkeys; isptr vvals;
              (forall x, (Int.min_signed <= keys m x <= Int.max_signed)))
         LOCAL (`(eq vkey) (eval_id _key);
                `(eq vbb) (eval_id _busybits);
                `(eq vkeys) (eval_id _keys);
                `(eq vvals) (eval_id _values))
         SEP (`(array_at tint sh (fun x =>
                                   (Vint (Int.repr (if (busybits m x)
                                                    then 1
                                                    else 0))))
                        0 100) (eval_id _busybits);
             `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                        0 100) (eval_id _keys);
             `(array_at tint sh (fun x => (Vint (Int.repr (values m x))))
                        0 100) (eval_id _values))
     POST [tint]
          PROP()
          LOCAL (`(match (amGet m key) with
                    |Some x => (eq (Vint (Int.repr x)))
                    |None => (eq (Vint (Int.repr (-1))))
                  end) retval)
          SEP (`(array_at tint sh (fun x =>
                                     (Vint (Int.repr (if (busybits m x)
                                                      then 1
                                                      else 0))))
                          0 100 vbb);
               `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                          0 100 vkeys);
               `(array_at tint sh (fun x => (Vint (Int.repr (values m x))))
                          0 100 vvals)).

Definition put_spec :=
  DECLARE _put
    WITH sh : share, m : ArrMapZ, key : Z, val : Z,
         vbb : val, vkeys : val, vvals : val, vkey : val, vval : val
    PRE [_busybits OF (tptr tint), _keys OF (tptr tint),
         _values OF (tptr tint), _key OF tint, _value OF tint]
        PROP (repr key vkey; repr val vval;
              isptr vbb; isptr vkeys; isptr vvals;
              writable_share sh)
        LOCAL (`(eq vkey) (eval_id _key);
               `(eq vval) (eval_id _value);
               `(eq vbb) (eval_id _busybits);
               `(eq vkeys) (eval_id _keys);
               `(eq vvals) (eval_id _values))
        SEP (`(array_at tint sh (fun x =>
                                   (Vint (Int.repr (if (busybits m x)
                                                    then 1
                                                    else 0))))
                        0 100) (eval_id _busybits);
             `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                        0 100) (eval_id _keys);
             `(array_at tint sh (fun x => (Vint (Int.repr (values m x))))
                        0 100) (eval_id _values))
    POST [tint] (match (amPut m key val) with
                   |Some ret => (`(array_at tint sh
                                           (fun x => (Vint (Int.repr
                                                              (if (busybits ret x)
                                                               then 1 else 0))))
                                           0 100 vbb) *
                                 `(array_at tint sh
                                           (fun x => (Vint (Int.repr (keys ret x))))
                                           0 100 vkeys) *
                                 `(array_at tint sh
                                           (fun x => (Vint (Int.repr (values ret x))))
                                           0 100 vvals))
                   |None => (local (`(eq (Vint (Int.repr (-1)))) retval))
                 end).

Definition Vprog : varspecs := nil.
Definition Gprog : funspecs := loop_spec :: find_empty_spec :: find_key_spec
                                         :: get_spec :: put_spec :: nil.


(* Helper tactics *)
Ltac unfold_int_limits :=
  
  unfold Int.min_signed, Int.max_signed, Int.half_modulus,
         Int.modulus, two_power_nat, Int.wordsize, Wordsize_32.wordsize,
         shift_nat, nat_iter;
  repeat match goal with
             |[H:context[Int.max_signed]|-_] =>
              unfold Int.min_signed, Int.max_signed, Int.half_modulus,
              Int.modulus, two_power_nat, Int.wordsize, Wordsize_32.wordsize,
              shift_nat, nat_iter in H
             |[H:context[Int.min_signed]|-_] =>
              unfold Int.min_signed, Int.max_signed, Int.half_modulus,
              Int.modulus, two_power_nat, Int.wordsize, Wordsize_32.wordsize,
              shift_nat, nat_iter in H
         end.

Ltac unfold_to_bare_Z :=
  unfold force_val, sem_mod, sem_add_default, sem_cast_neutral, sem_binarith;
  simpl;
  unfold both_int, sem_cast_neutral;
  simpl;
  unfold Int.mods;
  repeat rewrite Int.signed_repr;
  try (unfold_int_limits; simpl; omega);
  repeat rewrite add_repr;
  repeat rewrite sem_add_pi_ptr;
  repeat unfold force_val;
  repeat rewrite mul_repr.

Ltac auto_logic :=
  repeat rewrite andb_false_r; repeat rewrite andb_false_l; simpl; auto.

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
      |[H:?a = (Vint (Int.repr k))|-context[?a]] => rewrite H
      |[H:?a = (Int.repr Z.of_nat(k))|-context[Int.signed ?a]] =>
       rewrite H; rewrite Int.signed_repr;[|repr_bound k]
      |[H:?a = (Int.repr (Z.of_nat k))|-context[?a]] => rewrite H
      |[H:?a = (Vint (Int.repr (Z.of_nat k)))|-context[?a]] => rewrite H
      |[H:k = ?a|-context[?a]]=>rewrite <- H
      |[H:repr k (Vint ?a) |-context[?a]] =>
       let H' := fresh a "EQ" k in
       assert (a = (Int.repr k)) as H' by (inv H;tauto)
      |[H:repr k ?a |-context[?a]] =>
       let H' := fresh "EQ" k in
       assert (a = (Vint (Int.repr k))) as H' by (inv H; tauto)
      |[H1:repr k ?a, H2:?a = Vint ?b |-context[?b]] =>
       let H' := fresh "EQ" k in
       assert (a = (Vint (Int.repr k))) as H' by (inv H1; tauto);
         let Hinj := fresh "EQ" b in
         rewrite H' in H2; injection H2 as Hinj; symmetry in Hinj
      |[H1:Nrepr k ?a, H2:?a = Vint ?b |-context[?b]] =>
       let H' := fresh "EQ" k in
       assert (a = (Vint (Int.repr (Z.of_nat k)))) as H' by (inv H1; tauto);
         let Hinj := fresh "EQ" b in
         rewrite H' in H2; injection H2 as Hinj; symmetry in Hinj
    end.

(* Auxillary lemmas *)
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

Lemma int_if_false: forall expr:bool,
                      Int.eq (Int.repr 0)
                             (Int.repr (if expr then 1 else 0)) = true ->
                      expr = false.
Proof.
  intros.
  destruct expr.
  apply int_eq_e in H.
  discriminate H.
  tauto.
Qed.

Lemma int_modulus_eq: forall a b, Int.min_signed <= a <= Int.max_signed ->
                                  Int.min_signed <= b <= Int.max_signed ->
                                  ((Int.Z_mod_modulus a = Int.Z_mod_modulus b) <->
                                   (a = b)).
Proof.
  intros a b ABOUND BBOUND.
  rewrite Int.Z_mod_modulus_eq.
  rewrite Int.Z_mod_modulus_eq.
  unfold_int_limits.
  simpl in ABOUND, BBOUND.
  destruct a.
  - destruct b.
    + rewrite Zmod_small;[tauto|omega].
    + pose (Zgt_pos_0 p).
      rewrite Zmod_small;[|omega].
      rewrite Zmod_small;[tauto|omega].
    + pose (Zlt_neg_0 p).
      rewrite Zmod_small;[|omega].
      replace (Z.neg p mod 4294967296)
      with ((Z.neg p + 1*4294967296) mod 4294967296);[|apply Z_mod_plus_full].
      rewrite Zmod_small;omega.
  - pose (Zgt_pos_0 p); destruct b.
    + rewrite Zmod_small;[|omega].
      rewrite Zmod_small;omega.
    + rewrite Zmod_small;[|omega].
      pose (Zgt_pos_0 p0);rewrite Zmod_small;[tauto|omega].
    + pose (Zlt_neg_0 p0).
      replace (Z.neg p0 mod 4294967296)
      with ((Z.neg p0 + 1*4294967296) mod 4294967296);[|apply Z_mod_plus_full].
      rewrite Zmod_small;[|omega].
      rewrite Zmod_small;omega.
  - replace (Z.neg p mod 4294967296)
    with ((Z.neg p + 1*4294967296) mod 4294967296);[|apply Z_mod_plus_full].
    pose (Zlt_neg_0 p).
    rewrite Zmod_small;[|omega];destruct b.
    + rewrite Zmod_small;omega.
    + pose (Zgt_pos_0 p0).
      rewrite Zmod_small;omega.
    + pose (Zlt_neg_0 p0).
      replace (Z.neg p0 mod 4294967296)
      with ((Z.neg p0 + 1*4294967296) mod 4294967296);[|apply Z_mod_plus_full].
      rewrite Zmod_small;omega.
Qed.

Lemma Nrepr0_is_0 n i:
  Nrepr n (Vint i) -> Int.eq (Int.repr 0) i = true -> (0 = n)%nat.
Proof.
  inversion 1. subst. intro A.
  symmetry in A. apply binop_lemmas.int_eq_true in A.
  inv A.
  rewrite Int.Z_mod_modulus_eq in H1.
  rewrite <- Nat2Z.inj_iff.
  rewrite <- Zmod_small with (x:=Z.of_nat n) (y:=Int.modulus).
  simpl; assumption.
  split.
  - omega.
  - inv H2.
    rewrite Nat2Z.inj_le in H3.
    rewrite Z2Nat.id in H3.
    unfold_int_limits; simpl in H3; omega.
    unfold_int_limits; simpl; omega.
Qed.


Lemma Nrepr_neq_0 n i:
  Nrepr n (Vint i) -> Int.eq (Int.repr 0) i = false -> (n <> 0)%nat.
Proof.
  inversion 1. subst. intro A.
  SearchAbout Int.eq.
  pose (B:=Int.eq_spec  (Int.repr 0) (Int.repr (Z.of_nat n))).
  rewrite A in B.
  destruct n.
  simpl in B.
  auto.
  auto.
Qed.

(* Proofs for spec-body correspondence *)
Lemma body_loop: semax_body Vprog Gprog f_loop loop_spec.
Proof.
  start_function.
  name karg _k.
  forward.
  entailer!.
  - unfold_to_bare_Z.
    rewrite neq_100_mone.
    auto_logic.
    rewrite neq_100_mone.
    auto_logic.
  - rewrite neq_100_mone.
    auto_logic.
  - unfold_to_bare_Z.
    rewrite neq_100_mone.
    auto_logic.
  - unfold_to_bare_Z.
    rewrite neq_100_mone.
    auto_logic.
    unfold_to_bare_Z.
    unfold_to_bare_Z.
    unfold loop.
    get_repr k.
    + tauto.
    + assert (-100 <= Z.rem (Int.signed karg) 100 <= 100). {
        assert (Z.abs (Z.rem (Int.signed karg) 100) < Z.abs 100)
          by (apply Z.rem_bound_abs;omega).
        unfold Z.abs in H0.
        destruct (Z.rem (Int.signed karg) 100).
        - omega.
        - pose (Zgt_pos_0 p); omega.
        - pose (Zgt_pos_0 p).
          SearchAbout Z.pos.
          replace (Z.neg p) with (- Z.pos p);[|apply Pos2Z.opp_pos].
          omega.
      }
      unfold_to_bare_Z.
Qed.

Lemma body_find_empty: semax_body Vprog Gprog f_find_empty find_empty_spec.
Proof.
  start_function.
  name bbarg _busybits.
  name sarg _start.
  name iarg _i.
  name indexloc _index.
  name bbloc _bb.
  forward_call (sh,(start + Z.of_nat i + 1), (* loop(1 + start + i) *)
                (Vint (Int.repr (start + Z.of_nat i + 1)))). {
    entailer!. 
    - constructor.
      unfold_to_bare_Z.
    - get_repr start.
      get_repr i.
      unfold_to_bare_Z.
      apply f_equal;omega.
  }
  - auto with closed.
  - after_call.
    forward.
    pose (Loop_bound (start + Z.of_nat i + 1)).
    entailer!.
    apply Loop_bound.
    simpl;auto.
    forward_if (PROP (busybits m (loop (start + Z.of_nat i + 1)) = true)
                LOCAL (`(eq vi) (eval_id _i);
                       `(eq vstart) (eval_id _start);
                       `(eq vbb) (eval_id _busybits))
                SEP(`(array_at tint sh (fun x =>
                                    (Vint (Int.repr (if (busybits m x)
                                                     then 1
                                                     else 0))))
                         0 100 vbb))).
    + pose (Loop_bound (start + Z.of_nat i + 1)).
      forward. entailer!. rename H4 into BB.
      unfold find_empty.
      rewrite find_if_equation.
      rewrite Int.signed_repr in BB;[|unfold_to_bare_Z].
      apply int_if_false in BB.
      replace (1 + start + Z.of_nat i) with (start + Z.of_nat i + 1);[|omega].
      rewrite BB.
      simpl;tauto.
    + forward. entailer!. rename H4 into BB.
      rewrite Int.signed_repr in BB.
      * destruct ( busybits m (loop (start + Z.of_nat i + 1))).
        tauto.
        rewrite Int.eq_true in BB.
        discriminate BB.
      * pose (Loop_bound (start + Z.of_nat i + 1));unfold_to_bare_Z.
    + forward_if (PROP((0 < i)%nat;
                       busybits m (loop (start + Z.of_nat i + 1)) = true)
                  LOCAL(`(eq vi) (eval_id _i);
                        `(eq vstart) (eval_id _start);
                        `(eq vbb) (eval_id _busybits))
                  SEP(`(array_at tint sh (fun x =>
                                            (Vint (Int.repr (if (busybits m x)
                                                             then 1
                                                             else 0))))
                                 0 100 vbb))).
      * forward. entailer!. rename H4 into BB.
        replace (start + Z.of_nat i + 1)
        with (1 + start + Z.of_nat i) in BB;[|omega].
        assert (0=i)%nat by (apply Nrepr0_is_0 with iarg;assumption).
        subst i.
        unfold find_empty.
        rewrite find_if_equation.
        rewrite BB.
        auto_logic.
      * forward.
        entailer!.
        assert (i<>0)%nat by (apply Nrepr_neq_0 with iarg;assumption).
        omega.
      * forward_call(sh, m, start, (i - 1)%nat, vbb, vstart,
                     (Vint (Int.repr (Z.of_nat (i - 1))))). {
          entailer!. (* find_empty(busybits, start, i - 1) *)
          - replace (Vint sarg) with (vstart);assumption.
          - constructor.
            split.
            omega.
            apply Nat2Z.inj_le.
            rewrite Nat2Z.inj_sub;[|omega].
            rewrite Z2Nat.id;[|unfold_int_limits;simpl;omega].
            unfold_int_limits;simpl;omega.
          - rewrite Nat2Z.inj_sub;omega.
          - get_repr i.
            rewrite sub_repr.
            rewrite Nat2Z.inj_sub;[simpl;tauto|omega].
        }
        after_call.
        forward.
        entailer!. rename H5 into BB, H6 into FIN.
        unfold find_empty.
        rewrite find_if_equation.
        replace (start + Z.of_nat i + 1) with (1 + start + Z.of_nat i) in BB;[|omega].
        rewrite BB.
        simpl.
        destruct i;[omega|].
        unfold find_empty in FIN.
        replace (S i - 1)%nat with i in FIN;[|omega].
        assumption.
Qed.

Lemma body_find_key: semax_body Vprog Gprog f_find_key find_key_spec.
Proof.
  start_function.
  name bbarg _busybits.
  name ksarg _keys.
  name sarg _start.
  name keyarg _key.
  name iarg _i.
  name indexloc _index.
  name bbloc _bb.
  name kloc _k.
  forward_call (sh,(start + Z.of_nat i + 1), (* loop(1 + start + i) *)
                (Vint (Int.repr (start + Z.of_nat i + 1)))). {
    entailer!. 
    - constructor.
      unfold_to_bare_Z.
    - get_repr start.
      get_repr i.
      unfold_to_bare_Z.
      apply f_equal;omega.
  }
  - auto with closed.
  - after_call.
    forward.
    pose (Loop_bound (start + Z.of_nat i + 1)).
    entailer!.
    apply Loop_bound.
    simpl;auto.
    forward.
    pose (Loop_bound (start + Z.of_nat i + 1)).
    entailer!.
    apply Loop_bound.
    simpl;auto.
    (* pose (vk := Vint (Int.repr (keys m (loop (start + Z.of_nat i + 1))))).*)
    forward_if (PROP ((andb (busybits m (loop (start + Z.of_nat i + 1)))
                            (Z.eqb key (keys m (loop (start + Z.of_nat i + 1))))) = false)
                LOCAL (`(eq vi) (eval_id _i);
                       `(eq vstart) (eval_id _start);
                       `(eq vkey) (eval_id _key);
                       `(eq vbb) (eval_id _busybits);
                       `(eq vkeys) (eval_id _keys))
                SEP(`(array_at tint sh (fun x =>
                                          (Vint (Int.repr (if (busybits m x)
                                                           then 1
                                                           else 0))))
                               0 100 vbb);
                    `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                               0 100 vkeys))).
    + forward_if (PROP ((andb (busybits m (loop (start + Z.of_nat i + 1)))
                            (Z.eqb key (keys m (loop (start + Z.of_nat i + 1))))) = false)
                  LOCAL (`(eq vi) (eval_id _i);
                         `(eq vstart) (eval_id _start);
                         `(eq vkey) (eval_id _key);
                         `(eq vbb) (eval_id _busybits);
                         `(eq vkeys) (eval_id _keys))
                  SEP(`(array_at tint sh (fun x =>
                                            (Vint (Int.repr (if (busybits m x)
                                                             then 1
                                                             else 0))))
                                 0 100 vbb);
                      `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                                 0 100 vkeys))).
      * forward. entailer!. rename H7 into KEQ, H8 into BB, H6 into KEYSBOUND.
        rewrite Int.signed_repr in KEQ, BB.

        unfold find_key; rewrite find_if_equation.
        assert ((key =? keys m (loop (start + Z.of_nat i + 1))) = true) as KK.
        apply int_eq_e in KEQ.
        assert (keyarg = (Int.repr key)) as KREP by (get_repr key;tauto).
        rewrite KREP in KEQ.
        injection KEQ.
        rewrite int_modulus_eq.
        intro KEQK.
        rewrite KEQK.
        apply Z.eqb_eq;tauto.
        apply KEYSBOUND.
        repr_bound key.
        replace (1 + start + Z.of_nat i)
        with (start + Z.of_nat i + 1);[|omega].
        rewrite KK.
        destruct (busybits m (loop (start + Z.of_nat i + 1))).
        simpl;tauto.
        pose (EQSPEC:=Int.eq_spec (Int.repr 1) (Int.repr 0)).
        rewrite BB in EQSPEC.
        discriminate EQSPEC.
        pose (Loop_bound (start + Z.of_nat i + 1));unfold_to_bare_Z.
        pose (Loop_bound (start + Z.of_nat i + 1));unfold_to_bare_Z.
      * forward. entailer!. rename H7 into KEQ.
        rewrite Int.signed_repr in KEQ.
        destruct (Z.eq_dec key (keys m (loop (start + Z.of_nat i + 1)))) eqn:DE.
        rewrite <- e in KEQ.
        replace keyarg with (Int.repr key) in KEQ;[|get_repr key;tauto].
        rewrite Int.eq_true in KEQ.
        discriminate KEQ.
        replace (key =? keys m (loop (start + Z.of_nat i + 1)))
        with false;[|symmetry; apply Z.eqb_neq;assumption].
        auto_logic.
        pose (Loop_bound (start + Z.of_nat i + 1));unfold_to_bare_Z.
    + forward. entailer!. rename H7 into BB.
      rewrite Int.signed_repr in BB.
      assert (busybits m (loop (start + Z.of_nat i + 1)) = false) as FS. {
        destruct (busybits m (loop (start + Z.of_nat i + 1))).
        - rewrite Int.eq_true in BB; discriminate BB.
        - tauto.
      }
      rewrite FS.
      simpl;tauto.
      pose (Loop_bound (start + Z.of_nat i + 1));unfold_to_bare_Z.
    + forward_if (PROP((0 < i)%nat;
                       (andb (busybits m (loop (start + Z.of_nat i + 1)))
                            (Z.eqb key (keys m (loop (start + Z.of_nat i + 1))))) = false)
                  LOCAL(`(eq vi) (eval_id _i);
                        `(eq vstart) (eval_id _start);
                        `(eq vkey) (eval_id _key);
                        `(eq vbb) (eval_id _busybits);
                        `(eq vkeys) (eval_id _keys))
                  SEP(`(array_at tint sh (fun x =>
                                            (Vint (Int.repr (if (busybits m x)
                                                             then 1
                                                             else 0))))
                                 0 100 vbb);
                      `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                                 0 100 vkeys))).
      * forward. entailer!. rename H7 into COND.
        unfold find_key.
        rewrite find_if_equation.
        replace (1 + start + Z.of_nat i)
        with (start + Z.of_nat i + 1);[|omega].
        rewrite COND.
        assert (0=i)%nat. {
          apply Nrepr0_is_0 with iarg.
          - assumption.
          - rewrite Int.eq_sym;assumption.
        }
        subst i.
        tauto.
      * forward. entailer!.
        assert (i<>0)%nat. {
          apply Nrepr_neq_0 with iarg.
          - assumption.
          - rewrite Int.eq_sym;assumption.
        }
        omega.
      * forward_call(sh, m, start, key, (i - 1)%nat, vbb, vkeys,
                     vstart, vkey, (Vint (Int.repr (Z.of_nat (i - 1))))). {
          entailer!. (* find_key(busybits, keys, start, key, i - 1) *)
          - replace (Vint sarg) with (vstart);assumption.
          - replace (Vint keyarg) with (vkey);assumption.
          - constructor.
            split.
            omega.
            apply Nat2Z.inj_le.
            rewrite Nat2Z.inj_sub;[|omega].
            rewrite Z2Nat.id;[|unfold_int_limits;simpl;omega].
            unfold_int_limits;simpl;omega.
          - rewrite Nat2Z.inj_sub;omega.
          - get_repr i.
            rewrite sub_repr.
            rewrite Nat2Z.inj_sub;[simpl;tauto|omega].
        }
        after_call.
        forward.
        entailer!. rename H8 into COND, H9 into FIN.
        unfold find_key.
        rewrite find_if_equation.
        replace (start + Z.of_nat i + 1)
        with (1 + start + Z.of_nat i) in COND;[|omega].
        rewrite COND.
        destruct i;[omega|].
        unfold find_key in FIN.
        replace (S i - 1)%nat with i in FIN;[|omega].
        assumption.
Qed.

Lemma body_get: semax_body Vprog Gprog f_get get_spec.
Proof.
  start_function.
  name bbarg _busybits.
  name ksarg _keys.
  name valsarg _values.
  name karg _key.
  name startloc _start.
  name indexloc _index.
  forward_call(sh, key, vkey). {
    entailer!.
    rewrite <- H5;assumption.
  }
  auto with closed.
  after_call.
  forward_call(sh, m, loop key, key, 99%nat, vbb, vkeys,
                     Vint (Int.repr (loop key)), vkey, (Vint (Int.repr 99))). {
    pose (Loop_bound key).
    entailer!.
    - constructor; unfold_to_bare_Z.
    - rewrite <- H5;assumption.
    - constructor.
      split;[omega|].
      rewrite Nat2Z.inj_le.
      rewrite Z2Nat.id.
      unfold_to_bare_Z.
      unfold_to_bare_Z.
  }
  auto with closed.
  after_call.
  pose (vindex:=Vint (Int.repr (match find_key m (loop key) key 99 with
                                  |Some x => x
                                  |None => -1
                                end))).
  forward_if (PROP(None <> (find_key m (loop key) key 99))
                  LOCAL(`(eq vindex) (eval_id _index);
                        `(eq vbb) (eval_id _busybits);
                        `(eq vkeys) (eval_id _keys);
                        `(eq vvals) (eval_id _values))
                  SEP(`(array_at tint sh (fun x =>
                                            (Vint (Int.repr (if (busybits m x)
                                                             then 1
                                                             else 0))))
                                 0 100 vbb);
                      `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                                 0 100 vkeys);
                      `(array_at tint sh (fun x => (Vint (Int.repr (values m x))))
                                 0 100 vvals))).
  - forward. entailer!. rename H4 into IEQ, H5 into FIN.
    assert (indexloc = (Int.repr (-1))) as ILOC. {
      apply int_eq_e in IEQ.
      SearchAbout Int.neg.
      replace (-1) with (- (1));[|omega].
      rewrite <- Int.neg_repr.
      symmetry;assumption.
    }
    rewrite ILOC in FIN.
    assert (BND:=amFindKeyBound m key (loop key) 99).
    destruct (find_key m (loop key) key 99) eqn:FK.
    + injection FIN as ZEQ.
      replace 4294967295 with (Int.Z_mod_modulus (-1)) in ZEQ.
      rewrite int_modulus_eq in ZEQ.
      omega.
      unfold_to_bare_Z.
      unfold_to_bare_Z.
      rewrite Int.Z_mod_modulus_eq.
      replace (-1 mod Int.modulus)
      with ((-1 + 1*Int.modulus) mod Int.modulus);[|apply Z_mod_plus_full].
      rewrite Zmod_small;unfold_to_bare_Z.
    + unfold amGet.
      rewrite FK.
      auto.
  - forward. entailer!. rename H4 into IEQ, H5 into FIN.
    + destruct (find_key m (loop key) key 99).
      * discriminate.
      * replace (Int.neg (Int.repr 1)) with (Int.repr (-1)) in IEQ;[|auto].
        injection FIN as FIN'.
        rewrite FIN' in IEQ.
        rewrite Int.eq_true in IEQ.
        discriminate.
    + destruct (find_key m (loop key) key 99);subst vindex;assumption.
  - forward. assert (BND:=amFindKeyBound m key (loop key) 99).
    entailer!. rename H4 into FK.
    + destruct (find_key m (loop key) key 99).
      * rewrite Int.signed_repr;unfold_to_bare_Z.
      * tauto.
    + destruct (find_key m (loop key) key 99).
      * rewrite Int.signed_repr;unfold_to_bare_Z.
      * tauto.
    + simpl;auto.
    + forward. entailer!. rename H4 into FK.
      unfold amGet.
      assert (BND:=amFindKeyBound m key (loop key) 99).
      destruct (find_key m (loop key) key 99).
      * rewrite Int.signed_repr;[tauto|unfold_to_bare_Z].
      * tauto.
Qed.

Lemma body_put: semax_body Vprog Gprog f_put put_spec.
Proof.
  start_function.
  name bbarg _busybits.
  name ksarg _keys.
  name valsarg _values.
  name karg _key.
  name varg _value.
  name startloc _start.
  name indexloc _index.
  forward_call(sh, key, vkey). {
    entailer!.
    rewrite <- H6;assumption.
  }
  auto with closed.
  after_call.
  forward_call(sh, m, loop key, 99%nat, vbb,
                     Vint (Int.repr (loop key)), (Vint (Int.repr 99))). {
    pose (Loop_bound key).
    entailer!.
    - constructor; unfold_to_bare_Z.
    - constructor.
      split;[omega|].
      rewrite Nat2Z.inj_le.
      rewrite Z2Nat.id.
      unfold_to_bare_Z.
      unfold_to_bare_Z.
  }
  auto with closed.
  after_call.
  pose (vindex:=Vint (Int.repr (match find_empty m (loop key) 99 with
                                  |Some x => x
                                  |None => -1
                                end))).
  forward_if (PROP(None <> (find_empty m (loop key) 99))
                  LOCAL(`(eq vindex) (eval_id _index);
                        `(eq vkey) (eval_id _key);
                        `(eq vval) (eval_id _value);
                        `(eq vbb) (eval_id _busybits);
                        `(eq vkeys) (eval_id _keys);
                        `(eq vvals) (eval_id _values))
                  SEP(`(array_at tint sh (fun x =>
                                            (Vint (Int.repr (if (busybits m x)
                                                             then 1
                                                             else 0))))
                                 0 100 vbb);
                      `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                                 0 100 vkeys);
                      `(array_at tint sh (fun x => (Vint (Int.repr (values m x))))
                                 0 100 vvals))).
  - forward. entailer!. rename H6 into IEQ, H7 into FIN.
    assert (indexloc = (Int.repr (-1))) as ILOC. {
      apply int_eq_e in IEQ.
      SearchAbout Int.neg.
      replace (-1) with (- (1));[|omega].
      rewrite <- Int.neg_repr.
      symmetry;assumption.
    }
    rewrite ILOC in FIN.
    assert (BND:=amFindEmptyBound m (loop key) 99).
    destruct (find_empty m (loop key) 99) eqn:FK.
    + injection FIN as ZEQ.
      replace 4294967295 with (Int.Z_mod_modulus (-1)) in ZEQ.
      rewrite int_modulus_eq in ZEQ.
      omega.
      unfold_to_bare_Z.
      unfold_to_bare_Z.
      rewrite Int.Z_mod_modulus_eq.
      replace (-1 mod Int.modulus)
      with ((-1 + 1*Int.modulus) mod Int.modulus);[|apply Z_mod_plus_full].
      rewrite Zmod_small;unfold_to_bare_Z.
    + unfold amPut.
      rewrite FK.
      entailer.
  - forward. entailer!. rename H5 into IEQ, H6 into FIN.
    + destruct (find_empty m (loop key) 99).
      * discriminate.
      * replace (Int.neg (Int.repr 1)) with (Int.repr (-1)) in IEQ;[|auto].
        injection FIN as FIN'.
        rewrite FIN' in IEQ.
        rewrite Int.eq_true in IEQ.
        discriminate.
    + destruct (find_empty m (loop key) 99);subst vindex;assumption.
  - forward. {
      instantiate (2:=force_signed_int(vindex)).
      instantiate (1:=Vint (Int.repr 1)). 
      assert (BND:=amFindEmptyBound m (loop key) 99).
      destruct (find_empty m (loop key) 99) eqn: FE;[|tauto].
      entailer!.
      unfold force_signed_int, force_int.
      rewrite Int.signed_repr.
      rewrite <- H6.
      rewrite sem_add_pi_ptr.
      * unfold force_val.
        rewrite mul_repr.
        tauto.
      * assumption.
      * unfold_to_bare_Z.
      * unfold_to_bare_Z.
      * unfold_to_bare_Z.
    }
    forward. {
      instantiate (2:=force_signed_int(vindex)).
      instantiate (1:=Vint (Int.repr key)).
      assert (BND:=amFindEmptyBound m (loop key) 99).
      destruct (find_empty m (loop key) 99) eqn: FE;[|tauto].
      entailer!.
      unfold force_signed_int, force_int.
      rewrite Int.signed_repr.
      rewrite <- H6.
      rewrite sem_add_pi_ptr.
      * unfold force_val.
        rewrite mul_repr.
        tauto.
      * assumption.
      * unfold_to_bare_Z.
      * unfold_to_bare_Z.
      * unfold_to_bare_Z.
      * get_repr key.
        unfold_to_bare_Z;tauto.
    }
    forward. {
      instantiate (2:=force_signed_int(vindex)).
      instantiate (1:=Vint (Int.repr val)).
      assert (BND:=amFindEmptyBound m (loop key) 99).
      destruct (find_empty m (loop key) 99) eqn: FE;[|tauto].
      entailer!.
      unfold force_signed_int, force_int.
      rewrite Int.signed_repr.
      rewrite <- H6.
      rewrite sem_add_pi_ptr.
      * unfold force_val.
        rewrite mul_repr.
        tauto.
      * assumption.
      * unfold_to_bare_Z.
      * unfold_to_bare_Z.
      * unfold_to_bare_Z.
      * get_repr val.
        unfold_to_bare_Z;tauto.
    }
    forward.
    assert (BND:=amFindEmptyBound m (loop key) 99).
    destruct (find_empty m (loop key) 99) eqn: FE;[|tauto].
    assert (amPut m key val =
            Some {|values:= (fun (i:Z) =>
                               if (Z.eq_dec i z)
                               then val
                               else values m i);
                   keys:= (fun (i:Z) =>
                             if (Z.eq_dec i z)
                             then key
                             else keys m i);
                   busybits:= (fun (i:Z) =>
                                 if (Z.eq_dec i z)
                                 then true
                                 else busybits m i) |}) as PUT. {
      unfold amPut.
      rewrite FE.
      tauto.
    }
    pose (ret := {|
                  values := fun i : Z => if Z.eq_dec i z then val else values m i;
                  keys := fun i : Z => if Z.eq_dec i z then key else keys m i;
                  busybits := fun i : Z =>
                                if Z.eq_dec i z then true else busybits m i |}).
    assert ((upd (fun x : Z => Vint (Int.repr (if busybits m x then 1 else 0))) z
                 (Vint (Int.repr 1))) = 
            (fun x : Z =>
               Vint (Int.repr (if busybits ret x then 1 else 0)))). {
      unfold upd.
      unfold ret.
      apply functional_extensionality.
      intro.
      simpl.
      unfold initial_world.EqDec_Z, zeq.
      destruct (Z.eq_dec z x), (Z.eq_dec x z).
      - tauto.
      - subst z.
        tauto.
      - subst z;tauto.
      - tauto.
    }
    assert ((upd (fun x : Z => Vint (Int.repr (keys m x))) z
                 (Vint (Int.repr key))) = 
            (fun x : Z =>
               Vint (Int.repr (keys ret x)))). {
      unfold upd.
      unfold ret.
      apply functional_extensionality.
      intro.
      simpl.
      unfold initial_world.EqDec_Z, zeq.
      destruct (Z.eq_dec z x), (Z.eq_dec x z).
      - tauto.
      - rewrite e in n;tauto.
      - rewrite e in n;tauto.
      - tauto.
    }
    assert ((upd (fun x : Z => Vint (Int.repr (values m x))) z
                 (Vint (Int.repr val))) = 
            (fun x : Z =>
               Vint (Int.repr (values ret x)))). {
      unfold upd.
      unfold ret.
      apply functional_extensionality.
      intro.
      simpl.
      unfold initial_world.EqDec_Z, zeq.
      destruct (Z.eq_dec z x), (Z.eq_dec x z).
      - tauto.
      - rewrite e in n;tauto.
      - rewrite e in n;tauto.
      - tauto.
    }
    rewrite PUT.
    subst ret.
    rewrite <- H7.
    rewrite <- H8.
    rewrite <- H9.
    rewrite Int.signed_repr;[|unfold_to_bare_Z].
    entailer!.
Qed.

Existing Instance NullExtension.Espec.

Theorem all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_skipn.
semax_func_cons body_loop.
semax_func_cons body_find_empty.
semax_func_cons body_find_key.
semax_func_cons body_get.
semax_func_cons body_put.
apply semax_func_nil.
Qed.
