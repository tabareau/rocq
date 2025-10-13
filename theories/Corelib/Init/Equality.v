(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Notations.
Require Import Ltac.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Create HintDb typeclass_instances discriminated.
Create HintDb rewrite_instances discriminated.

Hint Constants Opaque : rewrite_instances.
Hint Projections Opaque : rewrite_instances.
Hint Variables Opaque : rewrite_instances.

Local Set Universe Polymorphism.

Class Has_refl@{sa se;la le} (A : Type@{sa ; la}) (x : A) (eq : A -> Type@{se;le})
:= refl : eq x.

Arguments refl {_ _} _ {_}.

(* This class register a Martin-Löf like elimination principle *)

Class Has_J@{sa se sp;la le lp} (A : Type@{sa ; la}) (x : A) (eq : A -> Type@{se;le})
  (Has_refl : Has_refl A x eq) :=
  J_eliminator : forall (P : forall y : A, eq y -> Type@{sp ; lp}), P x (refl eq) -> forall y e, P y e.

Class Has_J_r@{sa se sp;la le lp} (A : Type@{sa ; la}) (x : A) (eq : A -> Type@{se;le})
  (Has_refl : Has_refl A x eq) :=
  J_r_eliminator : forall (P : forall y : A, eq y -> Type@{sp ; lp}), forall y e, P y e -> P x (refl eq).

(* Those two classes are for dependent rewriting in an hypotesis *)

Class Has_J_forward@{sa se sp;la le lp} (A : Type@{sa ; la}) (x : A) (eq : A -> Type@{se;le})
  (Has_refl : Has_refl A x eq) :=
  J_forward : forall (P : forall y : A, eq y -> Type@{sp ; lp}) y e, P y e -> P x (refl eq).

Class Has_J_r_forward@{sa se sp;la le lp} (A : Type@{sa ; la}) (x : A) (eq : A -> Type@{se;le})
  (Has_refl : Has_refl A x eq) :=
  J_r_forward : forall (P : forall y : A, eq y -> Type@{sp ; lp}) y e, P y e -> P x (refl eq).

(* Those two classes are for non-dependent rewriting *)

Class Has_Leibniz@{sa se sp;la le lp} (A : Type@{sa ; la}) (x : A) (eq : A -> Type@{se;le}) :=
  leibniz : forall (P : A -> Type@{sp ; lp}), P x -> forall y, eq y -> P y.

Class Has_Leibniz_r@{sa se sp;la le lp} (A : Type@{sa ; la}) (x : A) (eq : A -> Type@{se;le}) :=
  leibniz_r : forall (P : A -> Type@{sp ; lp}) y, P y -> eq y -> P x.

Register Has_refl as rocq.core.Has_refl.
Typeclasses Opaque Has_refl.

Register Has_J as rocq.core.Has_J.
Typeclasses Opaque Has_J.

Register Has_J_r as rocq.core.Has_J_r.
Typeclasses Opaque Has_J_r.

Register Has_J_forward as rocq.core.Has_J_forward.
Typeclasses Opaque Has_J_forward.

Register Has_J_r_forward as rocq.core.Has_J_r_forward.
Typeclasses Opaque Has_J_r_forward.

Register Has_Leibniz as rocq.core.Has_Leibniz.
Typeclasses Opaque Has_Leibniz.

Register Has_Leibniz_r as rocq.core.Has_Leibniz_r.
Typeclasses Opaque Has_Leibniz_r.

Definition J_no_dep@{s s' sp;l l' lp} (A : Type@{s ; l}) (x : A) {eq} {refl} (eqr : Has_J@{s s' sp;l l' lp} A x eq refl) :
  forall (P : A -> Type@{sp ; lp}), P x -> forall y (e : eq y), P y :=
  fun P px y e => J_eliminator (fun y _ => P y) px y e.

Definition Has_J_Has_Leibniz@{s s' sp;l l' lp} (A : Type@{s ; l}) (x : A) {eq} {refl}
  (eqr : Has_J@{s s' sp;l l' lp} A x eq refl) : Has_Leibniz@{s s' sp;l l' lp} A x eq :=
  fun P px y e => J_no_dep A x eqr P px y e.

Section ap.
  Sort sa se sb se'.
  Universe la le lb le'.
  Context [A : Type@{sa;la}] [B:Type@{sb;lb}]
          (f : A -> B) (x:A)
          {eq : A -> Type@{se;le} }
          {eq' : B -> Type@{se';le'} }
          {_refl: Has_refl@{sb se';lb le'} B (f x) eq'}
          {_leibniz: Has_Leibniz@{sa se se';la le le'} A x eq}.

  Definition ap [y : A] (e : eq y) : eq' (f y) :=
    leibniz (fun y => eq' (f y)) (refl eq') y e.

End ap.

Register ap as rocq.core.ap.

Section sym.
  Sort sa se.
  Universe la le.
  Context {A : Type@{sa;la} } {x y :A}
          {eq : A -> A -> Type@{se;le} }
          {_refl: Has_refl@{sa se;la le} A x (eq x)}
          {_leibniz: Has_Leibniz@{sa se se;la le le} A x (eq x)}.

  Definition sym {y : A} (e : eq x y) : eq y x :=
    leibniz (fun y => eq y _) (refl (eq x)) _ e.

End sym.

Definition Has_J_Has_J_forward@{sa se sp;la le lp} {A : Type@{sa;la} } {x :A} eq Has_refl
  {has_J : Has_J@{sa se sp;la le lp} A x eq Has_refl} :
  forall (P : forall y : A, eq y -> Type@{sp ; lp}) y e,
      P y e -> P x (refl eq) :=
  fun P y e => J_eliminator (fun y e => P y e -> P _ _) (fun x => x) _ _.

Definition _Has_J_Has_J_forward@{sa se sp;la le lp} {A : Type@{sa;la} } {x :A} eq Has_refl
  {has_J : Has_J@{sa se sp;la le lp} A x eq Has_refl} : Has_J_forward@{sa se sp;la le lp} A x eq Has_refl
  := Has_J_Has_J_forward _ _.

Hint Resolve _Has_J_Has_J_forward : rewrite_instances.
