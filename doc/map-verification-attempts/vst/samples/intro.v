Require Import Omega.

Lemma f_inequal: forall (A B : Type) (f : A -> B) (x y : A), ~ f x = f y -> ~ x = y.
Proof.
intros A B f x y.
pose proof f_equal as FEQ.
assert (forall A B:Prop, (A -> B) -> (~B -> ~A)) by tauto.
apply H.
apply FEQ.
Qed.

Definition less_order (a b : nat) : Prop :=
  0 <= a < b.

Lemma less_order_nat_wf' : forall bound x:nat, x <= bound ->
                                              Acc less_order x.
Proof.
  intro bound. (*can not intro x, because need forall quantificator in IH *)
  unfold less_order.
  induction bound;constructor;intros.
  - omega.
  - apply IHbound.
    omega.
Qed.
