Require Import Utf8.
Require Import Lists.List.
Import ListNotations.


Section Relations_and_Ensembles.
Variable T : Type.

Definition relation : Type := T → T → Prop.
Definition ensemble : Type := T → Prop.
Definition image : relation → T → ensemble := fun R x => fun y => R x y.
Definition inverse_image : relation → T → ensemble := fun R x => fun y => R y x.

Section RelationKinds.
Variable R : relation.

Class Reflexive : Prop := reflCert : ∀ x : T, R x x.

Class Symmetric : Prop := symmCert : ∀ x y : T, R x y → R y x.

Class Asymmetric : Prop := asymCert : ∀ x y : T, R x y → ¬ R y x.

Class Transitive : Prop := transCert : ∀ x y z : T, R x y → R y z → R x z.

Class StrictOrder : Prop :=
{ so_asymConstr : Asymmetric
; so_transConstr : Transitive
}.

Class Equivalence : Prop :=
{ eq_reflConstr : Reflexive
; eq_symmConstr : Symmetric 
; eq_transConstr : Transitive
}.
End RelationKinds.

End Relations_and_Ensembles.

Arguments relation {T}.
Arguments ensemble {T}.
Arguments image {T}.
Arguments inverse_image {T}.
Arguments Reflexive {T}.
Arguments Symmetric {T}.
Arguments Asymmetric {T}.
Arguments Transitive {T}.
Arguments StrictOrder {T}.
Arguments Equivalence {T}.


(* -- Finitness ------------------------------------------------------------- *)
(*    for types ------------------------------------------------------------- *)
Class TFinite T : Prop := tfinCert : ∃ enum : list T, ∀ x : T, In x enum.
(*    for ensembles --------------------------------------------------------- *)
Class EFinite {T} (E : T → Prop) : Prop :=
  efinCert : ∃ enum : list T, ∀ x : T, E x → In x enum.


(* -- Positive Naturals ----------------------------------------------------- *)
Definition posnat : Set := {n : nat | n ≠ 0}.

Definition posnat_to_nat (x : posnat) : nat. 
Proof. destruct x. assumption. Defined.

Coercion posnat_to_nat : posnat >-> nat.

Definition nat_to_posnat (n : nat) : posnat.
Proof.
  assert (H : S n ≠ 0). discriminate.
  pose (p := exist (fun n : nat => n ≠ 0) (S n) H).
  exact p.
Defined.
