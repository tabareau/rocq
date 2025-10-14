
Module X.
  (*Set Universe Polymorphism.*)
  Inductive paths A (x : A) : forall _ : A, Type := idpath : paths A x x.
  Notation "x = y" := (@paths _ x y) (at level 70, no associativity) : type_scope.

  Definition paths_Has_Leibniz_elim : Has_Leibniz (@paths) :=
    fun A x P => @paths_rect A x (fun y _ => P y).
  Hint Resolve paths_Has_Leibniz_elim : rewrite_instances.

  Definition paths_Has_Leibniz_elim_r : Has_Leibniz_r (@paths).
  intros A x P t y e. now destruct e. Defined.
  Hint Resolve paths_Has_Leibniz_elim_r : rewrite_instances.

  Set Debug "rewrite".
  Set Debug "general_elim".
  Axioms A B : Type.
  Axiom P : A = B.
  Definition foo : A = B.
    abstract (rewrite P; rewrite <- P; reflexivity).
  Defined.
End X.

Module Y.
  (*Set Universe Polymorphism.*)
  Inductive paths A (x : A) : forall _ : A, Type := idpath : paths A x x.
  Notation "x = y" := (@paths _ x y) (at level 70, no associativity) : type_scope.

  Axioms A B : Type.
  Axiom P : A = B.

  Definition paths_Has_Leibniz_elim : Has_Leibniz (@paths) :=
    fun A x P => @paths_rect A x (fun y _ => P y).
  Hint Resolve paths_Has_Leibniz_elim : rewrite_instances.

  Definition paths_Has_Leibniz_elim_r : Has_Leibniz_r (@paths).
  intros A x P t y e. now destruct e. Defined.
  Hint Resolve paths_Has_Leibniz_elim_r : rewrite_instances.

  Definition foo : (A = B) * (A = B).
    split; abstract (rewrite <- P; reflexivity).
  Defined.
End Y.
