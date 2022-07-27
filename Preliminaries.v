Require Import Utf8.
Require Import Lists.List.
Import ListNotations.


(* -- Finitary types ---------------------------------------------- *)
Class Finite T : Prop :=
  fin_cert : ∃ enum : list T, ∀ x : T, In x enum.


(* -- Kinds of binary relations ----------------------------------- *)
Section BinaryRelations.
Variable T : Type.

  Definition relation : Type := T → T → Prop.

  Section BinaryRelationKinds.
  Variable R : relation.

    Class Reflexive : Prop := refl_cert : ∀ x : T, R x x.

    Class Symmetric : Prop := symm_cert : ∀ x y : T, R x y → R y x.

    Class Asymmetric : Prop := asym_cert : ∀ x y : T, R x y → ¬ R y x.

    Class Transitive : Prop := trns_cert : ∀ x y z : T, R x y → R y z → R x z.

    Class StrictOrder : Prop :=
    { so_asym_constr : Asymmetric
    ; so_trns_constr : Transitive }.

    Class Equivalence : Prop :=
    { eq_refl_constr : Reflexive
    ; eq_symm_constr : Symmetric
    ; eq_trns_constr : Transitive }.
  End BinaryRelationKinds.
End BinaryRelations.

Arguments relation {T}.
Arguments Reflexive {T}.
Arguments Symmetric {T}.
Arguments Asymmetric {T}.
Arguments Transitive {T}.
Arguments StrictOrder {T}.
Arguments Equivalence {T}.


(* Positive Naturals*)
Definition posnat : Set := {n : nat | n ≠ 0}.

Definition posnat_to_nat (x : posnat) : nat. 
Proof. destruct x. assumption. Defined.

Coercion posnat_to_nat : posnat >-> nat.


(* -- Some useful facts ------------------------------------------- *)
Instance unit_fin_cert : Finite unit.
Proof. exists [tt]. intro. destruct x. now left. Defined.