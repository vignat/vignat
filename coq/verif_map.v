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
              (Z.of_nat i < 261905)(*my max recursion depth*))
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
         PROP (repr key vkey; isptr vbb; isptr vkeys; isptr vvals)
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
                                           0 100 vbb) &&
                                 `(array_at tint sh
                                           (fun x => (Vint (Int.repr (keys ret x))))
                                           0 100 vkeys) &&
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

Lemma repr0_is_0 n i:
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


Lemma repr_neq_0 n i:
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
        assert (0=i)%nat by (apply repr0_is_0 with iarg;assumption).
        subst i.
        unfold find_empty.
        rewrite find_if_equation.
        rewrite BB.
        auto_logic.
      * forward.
        entailer!.
        assert (i<>0)%nat by (apply repr_neq_0 with iarg;assumption).
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
                       `(eq vbb) (eval_id _busybits);
                       `(eq vkey) (eval_id _key);
                       `(eq vkeys) (eval_id _keys))
                SEP(`(array_at tint sh (fun x =>
                                          (Vint (Int.repr (if (busybits m x)
                                                           then 1
                                                           else 0))))
                               0 100 vbb);
                    `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                               0 100 vkeys))).
    + forward_if (PROP (Z.eqb key (keys m (loop (start + Z.of_nat i + 1))) = false)
                  LOCAL (`(eq vi) (eval_id _i);
                         `(eq vstart) (eval_id _start);
                         `(eq vbb) (eval_id _busybits);
                         `(eq vkey) (eval_id _key);
                         `(eq vkeys) (eval_id _keys))
                  SEP(`(array_at tint sh (fun x =>
                                            (Vint (Int.repr (if (busybits m x)
                                                             then 1
                                                             else 0))))
                                 0 100 vbb);
                      `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                                 0 100 vkeys))).
      * forward. entailer!. rename H6 into KEQ, H7 into BB.
        rewrite Int.signed_repr in KEQ, BB.
        admit.
        pose (Loop_bound (start + Z.of_nat i + 1));unfold_to_bare_Z.
        pose (Loop_bound (start + Z.of_nat i + 1));unfold_to_bare_Z.
      * forward. entailer!.
                         admit.
      * admit.
    + forward. entailer!.
                       admit.
    + forward_if (PROP((0 < i)%nat;
                       (andb (busybits m (loop (start + Z.of_nat i + 1)))
                            (Z.eqb key (keys m (loop (start + Z.of_nat i + 1))))) = false)
                  LOCAL(`(eq vi) (eval_id _i);
                        `(eq vstart) (eval_id _start);
                        `(eq vbb) (eval_id _busybits);
                        `(eq vkey) (eval_id _key);
                        `(eq vkeys) (eval_id _keys))
                  SEP(`(array_at tint sh (fun x =>
                                            (Vint (Int.repr (if (busybits m x)
                                                             then 1
                                                             else 0))))
                                 0 100 vbb);
                      `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                                 0 100 vkeys))).
      * forward. entailer!.
        unfold find_key.
        rewrite find_if_equation.
        replace (1 + start + Z.of_nat i)
        with (start + Z.of_nat i + 1);[|omega].
        rewrite H6.
        assert (i = 0)%nat by admit.
        subst i.
        admit.
      * forward. entailer!.
                         admit.
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
        entailer!. rename H7 into COND, H8 into FIN.
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
