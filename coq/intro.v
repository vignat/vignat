
Lemma f_inequal: forall (A B : Type) (f : A -> B) (x y : A), ~ f x = f y -> ~ x = y.
Proof.
intros A B f x y.
pose proof f_equal as FEQ.
assert (forall A B:Prop, (A -> B) -> (~B -> ~A)) by tauto.
apply H.
apply FEQ.
Qed.