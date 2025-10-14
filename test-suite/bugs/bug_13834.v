Inductive myeq (A : Type) (x : A) : A -> Prop :=
| myeq_refl : myeq A x x.

Arguments myeq [A].
Arguments myeq_refl {A} {x}.

Definition myeq_Has_Leibniz_r_elim@{l} : Has_Leibniz_r@{Type Prop Prop | l Set Set} (@myeq).
intros A x P t y e. now destruct e.
Defined.

Hint Resolve myeq_Has_Leibniz_r_elim : rewrite_instances.

Definition myeq_Has_Leibniz_elim@{l} : Has_Leibniz@{Type Prop Prop | l Set Set} (@myeq).
intros A x P t y e. now destruct e.
Defined.

Hint Resolve myeq_Has_Leibniz_elim : rewrite_instances.

Definition myeqss (A : Type) (a b : A) (H : myeq (Some a) (Some b)) : myeq a b.
Proof.
  pose (Some b) as Someb.
  rewrite (myeq_refl : myeq (Some b) Someb) in *.
  pose proof (e := myeq_refl : myeq b (match Someb with None => a | Some b_ => b_ end)).
  rewrite e.
  destruct H.
  reflexivity.
Qed.
