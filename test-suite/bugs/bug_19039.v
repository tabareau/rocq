Set Universe Polymorphism.

Inductive eq@{s;u|} (A:Type@{s;u}) (x:A) : A -> Prop :=
  eq_refl : eq A x x.

Definition eq_Has_Leibniz_r_elim@{s s'; l l'} : Has_Leibniz_r@{s Prop s'; l Set l'} (@eq).
intros A x P t y e. now destruct e.
Defined.

Hint Resolve eq_Has_Leibniz_r_elim : rewrite_instances.

Inductive bool@{s; |} : Type@{s;Set} := true | false.

Lemma foo@{s; |} : forall (b : bool@{s;}),
    eq _ b true ->
    eq _ match b with
    | true => b
    | false => b end b.
Proof.
  intros b H.
  rewrite H.
  reflexivity.
Qed.
