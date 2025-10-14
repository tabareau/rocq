Polymorphic Inductive path {A : Type} (x : A) : A -> Type :=
  refl : path x x.

Definition path_Has_Leibniz_r_elim@{l l' l''} : Has_Leibniz_r@{Type Type Type | l l' l''} (@path@{l l'}).
intros A x P t y e. now destruct e.
Defined.

Hint Resolve path_Has_Leibniz_r_elim : rewrite_instances.

Goal False.
Proof.
simple refine (let H : False := _ in _).
+ exact_no_check I.
+ assert (path true false -> path false true).
  (** Create a dummy polymorphic side-effect *)
  {
    intro IHn.
    rewrite IHn.
    reflexivity.
  }
  exact H.
Fail Qed.
Abort.
