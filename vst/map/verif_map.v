Require Import floyd.proofauto.
Require Import map.
Require Import map_spec.
Require Import map_impl_spec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Psatz.

Local Open Scope logic.
Local Open Scope Z.

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
  unfold force_val, sem_mod, sem_add_default,
         sem_cast_neutral, sem_binarith in *;
  unfold both_int, sem_cast_neutral, Int.mods, force_val in *; simpl;
  try (unfold_int_limits; simpl; omega);
  try tauto.

Ltac auto_logic :=
  match goal with
    |[H:?x = false |-context[?x]] => rewrite H
    |[H:?x = false, A:context[?x]|-_] => rewrite H in A
    |[H:?x = true |-context[?x]] => rewrite H
    |[H:?x = true, A:context[?x]|-_] => rewrite H in A
    |[H:context[(?b && false)%bool]|-_] => rewrite andb_false_r in H
    |[|-context[(?b && false)%bool]] => rewrite andb_false_r
    |[H:context[(false && ?b)%bool]|-_] => rewrite andb_false_l in H
    |[|-context[(false && ?b)%bool]] => rewrite andb_false_l
  end.

Ltac repr_bound k :=
  match goal with
    |[H:repr k _ |-Int.min_signed <= k <= Int.max_signed] => inv H; assumption
    |[H:repr k _ |-context[Int.min_signed <= k]] => inv H
    |[H:repr k _ |-context[k <= Int.max_signed]] => inv H
  end.

Ltac does_not_have Z :=
  match goal with
    | _ : Z |- _ => fail 1
    | |- _ => idtac
  end.

Ltac int_eq_spec :=
  match goal with
    |[H:Int.eq ?a ?b = true|-_] =>
     does_not_have (a = b);
       let H' := fresh "EQSPEC" in
       assert (H':=Int.eq_spec a b);
         rewrite H in H'
    |[H:Int.eq ?a ?b = false|-_] =>
     does_not_have (a <> b);
       let H' := fresh "EQSPEC" in
       assert (H':=Int.eq_spec a b);
         rewrite H in H'
  end.

Ltac unfold_to_simpl :=
  match goal with
    |[H:context[force_val _] |-_] =>
     unfold force_val in H; simpl in H
    |[H:context[sem_sub_default _] |-_] =>
     unfold sem_sub_default in H; simpl H
  end.

Ltac int_arith :=
  match goal with
    |[|-context[Int.sub (Int.repr _) (Int.repr _)]] =>
     rewrite sub_repr
    |[H:context[Int.sub (Int.repr _) (Int.repr _)]|-_] =>
     rewrite sub_repr in H
    |[|-context[Int.add (Int.repr _) (Int.repr _)]] =>
     rewrite add_repr
    |[H:context[Int.add (Int.repr _) (Int.repr _)]|-_] =>
     rewrite add_repr in H
    |[|-context[Int.mul (Int.repr _) (Int.repr _)]] =>
     rewrite mul_repr
    |[H:context[Int.mul (Int.repr _) (Int.repr _)]|-_] =>
     rewrite mul_repr in H
    |[|-context[sem_add_pi _ _ (Vint _)]] =>
     rewrite sem_add_pi_ptr
    |[H:context[sem_add_pi _ _ (Vint _)]|-_] =>
     rewrite sem_add_pi_ptr in H
  end.

Ltac rebase_to_prev x:=
  let n := fresh "n" with
           P := fresh "PREV" x in
                 pose (n:=(x-1)%nat);
               assert (x = S n) as P by (subst n; omega);
               repeat match reverse goal with
                        |[|-context[x]] => rewrite P
                        |[H:context[x]|-_] => rewrite P in H
                      end;
               repeat match goal with
                        |[|-context[(S n - 1)%nat]] =>
                         replace (S n - 1)%nat with n;[|omega]
                        |[H:context[(S n - 1)%nat]|-_] =>
                         replace (S n - 1)%nat with n in H;[|omega]
                        |[H:context[(Z.of_nat (S n) - 1)]|-_] =>
                         replace (Z.of_nat (S n) - 1)
                         with (Z.of_nat n) in H;[|lia]
                      end.

Ltac nat2z :=
  match goal with
    |[|-context[Z.of_nat(_ + _)]] =>
     rewrite Nat2Z.inj_add
    |[H:context[Z.of_nat(_ + _)]|-_] =>
     rewrite Nat2Z.inj_add in H
    |[|-context[Z.of_nat(_ - _)]] =>
     rewrite Nat2Z.inj_sub
    |[H:context[Z.of_nat(_ - _)]|-_] =>
     rewrite Nat2Z.inj_sub in H
    |[|-context[_:nat = _:nat]] =>
     rewrite <- Nat2Z.inj_iff
    |[H:0 = Z.of_nat ?n|-_] =>
     does_not_have (n = 0)%nat;
       assert (n = 0)%nat by omega
    |[H:Z.of_nat ?n = 0|-_] =>
     does_not_have (n = 0)%nat;
       assert (n = 0)%nat by omega
    |[H:0 <> Z.of_nat ?n|-_] =>
     does_not_have (n <> 0)%nat;
       assert (n <> 0)%nat by omega
    |[H:Z.of_nat ?n <> 0|-_] =>
     does_not_have (n <> 0)%nat;
       assert (n <> 0)%nat by omega
  end.

Ltac solve_bound :=
  unfold_int_limits;
  match goal with
    |[|-context[(if ?c then 1 else 0)]] =>
     assert (0 <= (if c then 1 else 0) <= 1)
       by (destruct c;omega)
    |_ => idtac
  end;
  solve [auto|omega|simpl in *;omega].

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

Ltac eq_to_args :=
  match goal with
    |[H:Int.neg (Int.repr 1) = Int.repr ?a|-_] =>
     does_not_have (a = -1);
     let H' := fresh H "inj" in
     injection H as H';
       replace 4294967295 with (Int.Z_mod_modulus (-1) ) in H';[|auto];
       rewrite int_modulus_eq in H';[|solve_bound|solve_bound]
    |[H:Vint (Int.repr ?a) = Vint (Int.neg (Int.repr 1))|-_] =>
     does_not_have (a = -1);
     let H' := fresh H "inj" in
     injection H as H';
       replace 4294967295 with (Int.Z_mod_modulus (-1) ) in H';[|auto];
       rewrite int_modulus_eq in H';[|solve_bound|solve_bound]
    |[H:Vint (Int.repr ?a) = Vint (Int.neg _)|-_] => fail 1
    |[H:Vint ?a = Vint ?b |- _] =>
     does_not_have (a = b);
     let H' := fresh H "inj" in
     injection H as H'
    |[H:Int.repr ?a <> Int.repr ?b|-_] =>
     does_not_have (a <> b);
     let H':= fresh H "ns" in
     assert (a <> b) as H' by
                         (destruct (Z.eq_dec a b);
                          [assert (Int.repr a = Int.repr b) by
                              (apply f_equal;tauto);tauto|
                           auto])
    |[H:Int.repr ?a = Int.repr ?b|-_] =>
     does_not_have (a = b);
     let H' := fresh H "inj" in
     injection H as H'; 
       ((rewrite Int.Z_mod_modulus_eq in H';
         rewrite Z.mod_small in H';[|solve_bound] )
          || (rewrite int_modulus_eq in H';[|solve_bound|solve_bound]))
    |[|-Int.repr ?a = Int.repr ?b] =>
     apply f_equal
  end.

Ltac gr k :=
  match goal with
    |[H:repr k ?a |-_] =>
     does_not_have (a = (Vint (Int.repr k)));
       let H' := fresh "EQ" k with
                 BND := fresh k "BND" in
                         assert (a = (Vint (Int.repr k)))
                       as H' by (inv H; tauto);
                       assert (Int.min_signed <= k <= Int.max_signed)
                          as BND by (repr_bound k)
    |[H:Nrepr k ?a |-_] =>
     does_not_have (a = (Vint (Int.repr (Z.of_nat k))));
       let H' := fresh "EQ" k with
                 BND := fresh k "BND" in
                         assert (a = (Vint (Int.repr (Z.of_nat k))))
                       as H' by (inv H; tauto);
                       assert (0 <= Z.of_nat k <= Int.max_signed)
                          as BND by (inv H; tauto)
  end.

Ltac unfold_if :=
      match goal with
        |[H:?x = (if ?c then ?x else ?y)|-_] =>
         does_not_have (c = true);
           let H' := fresh H "b" in
           assert (c = true) as H' by (destruct c;auto)
        |[H:?x <> (if ?c then ?x else ?y)|-_] =>
         does_not_have (c = false);
           let H' := fresh H "b" in
           assert (c = false) as H' by (destruct c;auto)
        |[H:?y = (if ?c then ?x else ?y)|-_] =>
         does_not_have (c = false);
           let H' := fresh H "b" in
           assert (c = false) as H' by (destruct c;auto)
        |[H:?y <> (if ?c then ?x else ?y)|-_] =>
         does_not_have (c = true);
           let H' := fresh H "b" in
           assert (c = true) as H' by (destruct c;auto)
      end.

Ltac less_val :=
  match goal with
    |[x:val, H:?x = _|-_] => subst x
    |[x:int, H:?x = _|-_] => subst x
    |[x:val, H:_ = ?x|-_] => subst x
    |[x:int, H:_ = ?x|-_] => subst x
    |[x:Z, H:?x = 0|-_] => subst x
    |[x:nat, H:?x = 0|-_] => subst x
    |[H:eval_id ?x ?rho = _ |- context[eval_id ?x ?rho]] => rewrite H
    |[H:_ = eval_id ?x ?rho |- context[eval_id ?x ?rho]] => rewrite <- H
  end.

Ltac get_all_reprs :=
  repeat match goal with
           |[H:repr ?a _|-_] => gr a
           |[H:Nrepr ?a _|-_] => gr a
         end.

Ltac handle_signed :=
  match goal with
    |[H:context[Int.signed (Int.repr _)]|-_] =>
     rewrite Int.signed_repr in H;[|solve_bound]
    |[|-context[Int.signed (Int.repr _)]] =>
     rewrite Int.signed_repr;[|solve_bound]
  end.

Ltac eqb_from_eq :=
  match goal with
    |[H:?a = ?b |-context[?a =? ?b]] =>
     does_not_have (a =? b = true);
     let H' := fresh H "b" in
     assert (a =? b = true)
       as H' by (apply Z.eqb_eq;auto)
    |[H:?b = ?a |-context[?a =? ?b]] =>
     does_not_have (a =? b = true);
     let H' := fresh H "b" in
     assert (a =? b = true)
       as H' by (apply Z.eqb_eq;auto)
    |[H:?a <> ?b |-context[?a =? ?b]] =>
     does_not_have ((a =? b) = false);
       let H' := fresh H "b" in
       assert ((a =? b) = false)
         as H' by (apply Z.eqb_neq;auto)
    |[H:?b <> ?a |-context[?a =? ?b]] =>
     does_not_have ((a =? b) = false);
       let H' := fresh H "b" in
       assert ((a =? b) = false)
         as H' by (apply Z.eqb_neq;auto)
    |[|-context[?a =? ?a]] => rewrite Z.eqb_refl
  end.

Ltac to_abstract :=
  get_all_reprs;
  unfold_to_bare_Z;
  repeat (less_val || eq_to_args || int_arith || eqb_from_eq ||
                   (handle_signed;repeat handle_signed) || int_eq_spec ||
                   unfold_if || (auto_logic;repeat auto_logic) ||
                   rewrite neq_100_mone || (progress simpl)).

(* Auxillary lemmas *)
Lemma rem_bound: forall a b, b > 0 -> -b < Z.rem a b < b.
Proof.
  intros.
  assert (Z.abs (Z.rem a b) < Z.abs b) as ABS
    by (apply Z.rem_bound_abs;omega).
  unfold Z.abs in ABS.
  destruct b;[omega| |pose (Zlt_neg_0 p);omega].
  destruct (Z.rem a (Z.pos p)).
  - omega.
  - pose (Zgt_pos_0 p0); omega.
  - pose (Zgt_pos_0 p0).
    replace (Z.neg p0) with (- Z.pos p0);[|apply Pos2Z.opp_pos].
    omega.
Qed.

(* Prohibit for simpl tactic to expand 1+x into an ugly match *)
Arguments Z.add _ _ : simpl nomatch.

(* Proofs for spec-body correspondence *)
Lemma body_loop: semax_body Vprog Gprog f_loop loop_spec.
Proof.
  start_function.
  name karg _k.
  forward.
  unfold loop.
  assert (- (100) < Z.rem k 100 < 100)
    by (apply rem_bound;omega).
  entailer!;to_abstract;tauto.
Qed.

Lemma body_find_empty: semax_body Vprog Gprog f_find_empty find_empty_spec.
Proof.
  start_function.
  name bbarg _busybits.
  name sarg _start.
  name iarg _i.
  name indexloc _index.
  name bbloc _bb.
  forward_call (sh,(1 + start + Z.of_nat i), (* loop(1 + start + i) *)
                (Vint (Int.repr (1 + start + Z.of_nat i)))). {
    entailer!. 
    - constructor.
      to_abstract.
    - to_abstract;tauto.
  }
  - auto with closed.
  - after_call.
    forward.
    pose (Loop_bound (1 + start + Z.of_nat i)).
    entailer!;[apply Loop_bound|simpl;auto].
    forward_if (PROP (busybits m (loop (1 + start + Z.of_nat i)) = true)
                LOCAL (`(eq vi) (eval_id _i);
                       `(eq vstart) (eval_id _start);
                       `(eq vbb) (eval_id _busybits))
                SEP(`(array_at tint sh (fun x =>
                                    (Vint (Int.repr (if (busybits m x)
                                                     then 1
                                                     else 0))))
                         0 100 vbb))).
    + pose (Loop_bound (1 + start + Z.of_nat i)).
      forward. entailer!. rename H4 into BB.
      unfold find_empty.
      rewrite find_if_equation.
      to_abstract;tauto.
    + forward. entailer!. rename H4 into BB.
      pose (Loop_bound (1 + start + Z.of_nat i)).
      to_abstract;tauto.
    + forward_if (PROP((0 < i)%nat;
                       busybits m (loop (1 + start + Z.of_nat i)) = true)
                  LOCAL(`(eq vi) (eval_id _i);
                        `(eq vstart) (eval_id _start);
                        `(eq vbb) (eval_id _busybits))
                  SEP(`(array_at tint sh (fun x =>
                                            (Vint (Int.repr (if (busybits m x)
                                                             then 1
                                                             else 0))))
                                 0 100 vbb))).
      * forward. entailer!. rename H4 into BB.
        unfold find_empty; rewrite find_if_equation.
        to_abstract;nat2z;to_abstract;tauto.
      * forward.
        entailer!.
        to_abstract;omega.
      * forward_call(sh, m, start, (i - 1)%nat, vbb, vstart,
                     (Vint (Int.repr (Z.of_nat (i - 1))))). {
          entailer!. (* find_empty(busybits, start, i - 1) *)
          - to_abstract;constructor;assumption.
          - constructor.
            nat2z;unfold_to_bare_Z.
          - nat2z;omega.
          - to_abstract.
            nat2z;simpl;omega.
        }
        after_call.
        forward.
        entailer!. rename H6 into FIN.
        unfold find_empty in *.
        rewrite find_if_equation.
        to_abstract.
        rebase_to_prev i.
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
  forward_call (sh,(1 + start + Z.of_nat i), (* loop(1 + start + i) *)
                (Vint (Int.repr (1 + start + Z.of_nat i)))). {
    entailer!. 
    - constructor; to_abstract.
    - to_abstract;tauto.
  }
  - auto with closed.
  - after_call.
    forward.
    pose (Loop_bound (1 + start + Z.of_nat i)).
    entailer!;[apply Loop_bound|simpl;auto].
    forward.
    pose (Loop_bound (1 + start + Z.of_nat i)).
    entailer!;[apply Loop_bound|simpl;auto].
    forward_if (PROP ((andb (busybits m (loop (1 + start + Z.of_nat i)))
                            (Z.eqb key (keys m (loop (1 + start + Z.of_nat i))))) = false)
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
    + forward_if (PROP ((andb (busybits m (loop (1 + start + Z.of_nat i)))
                            (Z.eqb key (keys m (loop (1 + start + Z.of_nat i))))) = false)
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
        pose (Loop_bound (1 + start + Z.of_nat i)).
        unfold find_key; rewrite find_if_equation.
        to_abstract. 
        tauto.
      * forward. entailer!. rename H7 into KEQ.
        pose (Loop_bound (1 + start + Z.of_nat i)).
        to_abstract;tauto.
    + forward. entailer!. rename H7 into BB.
      pose (Loop_bound (1 + start + Z.of_nat i)).
      to_abstract;tauto.
    + forward_if (PROP((0 < i)%nat;
                       (andb (busybits m (loop (1 + start + Z.of_nat i)))
                            (Z.eqb key (keys m (loop (1 + start + Z.of_nat i))))) = false)
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
        unfold find_key; rewrite find_if_equation.
        to_abstract;nat2z;to_abstract;tauto.
      * forward. entailer!.
        to_abstract.
        nat2z;omega.
      * forward_call(sh, m, start, key, (i - 1)%nat, vbb, vkeys,
                     vstart, vkey, (Vint (Int.repr (Z.of_nat (i - 1))))). {
          entailer!. (* find_key(busybits, keys, start, key, i - 1) *)
          - to_abstract. constructor. assumption.
          - to_abstract. constructor;assumption.
          - to_abstract. constructor. nat2z;solve_bound.
          - nat2z;solve_bound.
          - to_abstract. nat2z;auto.
        }
        after_call.
        forward.
        entailer!. rename H8 into COND, H9 into FIN.
        unfold find_key in *.
        rewrite find_if_equation.
        to_abstract.
        rebase_to_prev i.
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
    entailer!. (* loop(key) *)
    to_abstract;constructor;solve_bound.
  }
  auto with closed.
  after_call.
  forward_call(sh, m, loop key, key, 99%nat, vbb, vkeys,
                     Vint (Int.repr (loop key)), vkey, (Vint (Int.repr 99))). {
    pose (Loop_bound key).
    entailer!.
    - constructor; solve_bound.
    - to_abstract;constructor;solve_bound.
    - constructor;solve_bound.
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
    assert (BND:=amFindKeyBound m key (loop key) 99).
    unfold amGet.
    to_abstract.
    destruct (find_key m (loop key) key 99) eqn:FK.
    + to_abstract.
      omega.
    + auto.
  - forward. entailer!. rename H4 into IEQ, H5 into FIN.
    + destruct (find_key m (loop key) key 99).
      * discriminate.
      * to_abstract. auto.
    + destruct (find_key m (loop key) key 99);subst vindex;assumption.
  - forward. assert (BND:=amFindKeyBound m key (loop key) 99).
    entailer!. rename H4 into FK.
    + destruct (find_key m (loop key) key 99).
      * to_abstract; omega.
      * tauto.
    + destruct (find_key m (loop key) key 99).
      * to_abstract;omega.
      * tauto.
    + simpl;auto.
    + forward. entailer!. rename H4 into FK.
      unfold amGet.
      assert (BND:=amFindKeyBound m key (loop key) 99).
      destruct (find_key m (loop key) key 99).
      * to_abstract;tauto.
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
    to_abstract;constructor;solve_bound.
  }
  auto with closed.
  after_call.
  forward_call(sh, m, loop key, 99%nat, vbb,
                     Vint (Int.repr (loop key)), (Vint (Int.repr 99))). {
    pose (Loop_bound key).
    entailer!.
    - constructor;solve_bound.
    - constructor;solve_bound.
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
    assert (BND:=amFindEmptyBound m (loop key) 99).
    to_abstract.
    destruct (find_empty m (loop key) 99) eqn:FE.
    + to_abstract.
      omega.
    + unfold amPut.
      rewrite FE.
      entailer.
  - forward. entailer!. rename H5 into IEQ, H6 into FIN.
    + destruct (find_empty m (loop key) 99).
      * discriminate.
      * to_abstract.
        auto.
    + destruct (find_empty m (loop key) 99);subst vindex;assumption.
  - forward. {
      instantiate (2:=force_signed_int(vindex)).
      instantiate (1:=Vint (Int.repr 1)). 
      assert (BND:=amFindEmptyBound m (loop key) 99).
      destruct (find_empty m (loop key) 99) eqn: FE;[|tauto].
      entailer!;to_abstract;auto;omega.
    }
    forward. {
      instantiate (2:=force_signed_int(vindex)).
      instantiate (1:=Vint (Int.repr key)).
      assert (BND:=amFindEmptyBound m (loop key) 99).
      destruct (find_empty m (loop key) 99) eqn: FE;[|tauto].
      entailer!;to_abstract;auto;omega.
    }
    forward. {
      instantiate (2:=force_signed_int(vindex)).
      instantiate (1:=Vint (Int.repr val)).
      assert (BND:=amFindEmptyBound m (loop key) 99).
      destruct (find_empty m (loop key) 99) eqn: FE;[|tauto].
      entailer!;to_abstract;auto;omega.
    }
    forward.
    assert (BND:=amFindEmptyBound m (loop key) 99).
    destruct (find_empty m (loop key) 99) eqn: FE;[|tauto].

    pose (ret := {|
                  values := fun i : Z => if Z.eq_dec i z then val else values m i;
                  keys := fun i : Z => if Z.eq_dec i z then key else keys m i;
                  busybits := fun i : Z =>
                                if Z.eq_dec i z then true else busybits m i |}).
    assert ((upd (fun x : Z => Vint (Int.repr (if busybits m x then 1 else 0)))
                 z (Vint (Int.repr 1))) = 
            (fun x : Z =>
               Vint (Int.repr (if busybits ret x then 1 else 0)))) as BBEQ. {
      unfold upd;unfold ret;apply functional_extensionality;intro;simpl.
      unfold initial_world.EqDec_Z, zeq.
      destruct (Z.eq_dec z x), (Z.eq_dec x z);to_abstract;tauto.
    }
    assert ((upd (fun x : Z => Vint (Int.repr (keys m x))) z
                 (Vint (Int.repr key))) = 
            (fun x : Z => Vint (Int.repr (keys ret x)))) as KEYSEQ. {
      unfold upd;unfold ret;apply functional_extensionality;intro;simpl.
      unfold initial_world.EqDec_Z, zeq.
      destruct (Z.eq_dec z x), (Z.eq_dec x z);to_abstract;tauto.
    }
    assert ((upd (fun x : Z => Vint (Int.repr (values m x))) z
                 (Vint (Int.repr val))) = 
            (fun x : Z => Vint (Int.repr (values ret x)))) as VALSEQ. {
      unfold upd;unfold ret;apply functional_extensionality;intro;simpl.
      unfold initial_world.EqDec_Z, zeq.
      destruct (Z.eq_dec z x), (Z.eq_dec x z);to_abstract;tauto.
    }
    unfold amPut.
    rewrite FE.
    subst ret.
    rewrite <- BBEQ.
    rewrite <- KEYSEQ.
    rewrite <- VALSEQ.
    to_abstract.
    entailer!.
Qed.

Lemma body_erase: semax_body Vprog Gprog f_erase erase_spec.
Proof.
  start_function.
  name bbarg _busybits.
  name ksarg _keys.
  name karg _key.
  name startloc _start.
  name indexloc _index.
  forward_call(sh, key, vkey). {
    entailer!.
    to_abstract;constructor;solve_bound.
  }
  auto with closed.
  after_call.
  forward_call(sh, m, loop key, key, 99%nat, vbb, vkeys,
                     Vint (Int.repr (loop key)), vkey, (Vint (Int.repr 99))). {
    pose (Loop_bound key).
    entailer!.
    - constructor;solve_bound.
    - to_abstract;assumption. 
    - constructor;solve_bound.
  }
  auto with closed.
  after_call.
  pose (vindex:=Vint (Int.repr (match find_key m (loop key) key 99 with
                                  |Some x => x
                                  |None => -1
                                end))).
  forward_if (PROP(None <> (find_key m (loop key) key 99))
                  LOCAL(`(eq vindex) (eval_id _index);
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
  - forward. entailer!. rename H5 into IEQ, H6 into FIN.
    assert (BND:=amFindKeyBound m key (loop key) 99).
    destruct (find_key m (loop key) key 99) eqn:FK.
    + to_abstract;omega.
    + unfold amErase.
      rewrite FK.
      entailer.
  - forward. entailer!. rename H4 into IEQ, H5 into FIN.
    + destruct (find_key m (loop key) key 99).
      * discriminate.
      * to_abstract; auto.
    + destruct (find_key m (loop key) key 99);subst vindex;assumption.
  - forward. {
      instantiate (2:=force_signed_int(vindex)).
      instantiate (1:=Vint (Int.repr 0)). 
      assert (BND:=amFindKeyBound m key (loop key) 99).
      destruct (find_key m (loop key) key 99) eqn: FE;[|tauto].
      entailer!;to_abstract;auto;omega.
    }
    forward.
    assert (BND:=amFindKeyBound m key (loop key) 99).
    destruct (find_key m (loop key) key 99) eqn: FE;[|tauto].

    pose (ret := {|
                  values := values m;
                  keys := keys m;
                  busybits := fun i : Z =>
                                if Z.eq_dec i z then false else busybits m i |}).
    assert ((upd (fun x : Z => Vint (Int.repr (if busybits m x then 1 else 0)))
                 z (Vint (Int.repr 0))) = 
            (fun x : Z =>
               Vint (Int.repr (if busybits ret x then 1 else 0)))) as BBEQ. {
      unfold upd;unfold ret;apply functional_extensionality;intro;simpl.
      unfold initial_world.EqDec_Z, zeq.
      destruct (Z.eq_dec z x), (Z.eq_dec x z);to_abstract;tauto.
    }
    unfold amErase.
    rewrite FE.
    subst ret.
    rewrite <- BBEQ.
    to_abstract.
    entailer!.
Qed.

Lemma body_size_rec: semax_body Vprog Gprog f_size_rec size_rec_spec.
Proof.
  start_function.
  name iarg _i.
  name bbarg _busybits.
  name indexloc _index.
  name bbloc _bb.
  forward_if (PROP((0 < i)%nat)
              LOCAL(`(eq vi) (eval_id _i);
                    `(eq vbb) (eval_id _busybits))
              SEP(`(array_at tint sh (fun x =>
                                        (Vint (Int.repr (if (busybits m x)
                                                         then 1
                                                         else 0))))
                             0 100 vbb))).
  - forward. entailer!.
    to_abstract;nat2z;to_abstract;tauto.
  - forward. entailer!.
    to_abstract;nat2z;omega.
  - forward. forward.
    to_abstract.
    simpl in H3;to_abstract.
    entailer!;[omega|simpl;tauto].
    forward_if (PROP (busybits m (Z.of_nat i - 1) = false;
                     (0 < i)%nat)
                LOCAL (`(eq vi) (eval_id _i);
                       `(eq vbb) (eval_id _busybits))
                SEP(`(array_at tint sh (fun x =>
                                    (Vint (Int.repr (if (busybits m x)
                                                     then 1
                                                     else 0))))
                         0 100 vbb))).
    + forward_call (sh,m, (i - 1)%nat, (* size_rec(busybits, i-1) *)
                    vbb, (Vint (Int.repr (Z.of_nat (i - 1))))). {
        entailer!.
        - lia.
        - constructor;nat2z;solve_bound.
        - to_abstract;nat2z;solve_bound.
      }
      * after_call.
        forward. entailer!.
        to_abstract.
        simpl in H4.
        to_abstract.
        rebase_to_prev i.
        unfold amPartSize;fold amPartSize.
        rewrite EQSPECinjb.
        lia.
    + forward. entailer!.
      to_abstract.
      simpl in H4.
      to_abstract.
      tauto.
    + forward_call (sh,m, (i - 1)%nat, (* size_rec(busybits, i-1) *)
                    vbb, (Vint (Int.repr (Z.of_nat (i - 1))))). {
      entailer!.
      - lia.
      - constructor;nat2z;solve_bound.
      - to_abstract;nat2z;solve_bound.
      }
      after_call.
      forward. entailer!.
      rebase_to_prev i.
      unfold amPartSize; fold amPartSize.
      to_abstract;tauto.
Qed.

Lemma body_size: semax_body Vprog Gprog f_size size_spec.
Proof.
  start_function.
  name bbarg _busybits.
  forward_call (sh, m, 100%nat, (* size_rec(busybits, 100) *)
                vbb, (Vint (Int.repr 100))). {
    entailer!.
    constructor;unfold_int_limits;simpl;omega.
  }
  after_call.      
  forward.
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
semax_func_cons body_erase.
semax_func_cons body_size_rec.
semax_func_cons body_size.
apply semax_func_nil.
Qed.
