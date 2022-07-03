Require Import Lists.List.
Require Export Relations.Relation_Definitions.
Import ListNotations.


(* -- Finitary types ---------------------------------------------- *)
Class Finite T : Prop :=
  fin_cert : exists enum : list T, forall x : T, In x enum.


(* -- Kinds of binary relations ----------------------------------- *)
Class Reflexive {T} (R : relation T) : Prop :=
  refl_cert : forall x : T, R x x.

Class Symmetric {T} (R : relation T) : Prop :=
  symm_cert : forall x y : T, R x y -> R y x.

Class Asymmetric {T} (R : relation T) : Prop :=
  asym_cert : forall x y : T, R x y -> ~ R y x.

Class Transitive {T} (R : relation T) : Prop :=
  trns_cert : forall x y z : T, R x y -> R y z -> R x z.

Class StrictOrder {T} (R : relation T) : Prop :=
{ so_asym_constr : Asymmetric R
; so_trns_constr : Transitive R }.

Class Equivalence {T} (R : relation T) : Prop :=
{ eq_refl_constr : Reflexive R
; eq_symm_constr : Symmetric R
; eq_trns_constr : Transitive R
}.


(* -- Some useful facts ------------------------------------------- *)
Instance unit_fin_cert : Finite unit.
Proof. exists [tt]. intro. destruct x. now left. Defined.