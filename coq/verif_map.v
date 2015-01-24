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

Inductive Irepr : nat -> val -> Prop :=
| mk_Irepr : forall i:nat, (0 <= i <= Z.to_nat(Int.max_signed))%nat ->
                           Irepr i (Vint (Int.repr (Z.of_nat i))).

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
        PROP (0 <= start < 100; repr start vstart; Irepr i vi;
              isptr vbb)
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
        PROP (0 <= start < 100; repr start vstart; repr key vkey;
              Irepr i vi; isptr vbb; isptr vkeys)
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
                         0 100) (eval_id _busybits);
              `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                         0 100) (eval_id _keys)).

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
                          0 100) (eval_id _busybits);
               `(array_at tint sh (fun x => (Vint (Int.repr (keys m x))))
                          0 100) (eval_id _keys);
               `(array_at tint sh (fun x => (Vint (Int.repr (values m x))))
                          0 100) (eval_id _values)).

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
  simpl.

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
