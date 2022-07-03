Require Import Lists.List.
Import ListNotations.


Class Clockable (C : Set) : Set :=
{ clock_fin : exists e : list C, forall c : C, In c e
; clock_dec : forall c' c'' : C, {c' = c''} + {c' <> c''} }.

Instance unit_clockable : Clockable unit.
Proof.
  constructor.
  - exists [tt]. intro. destruct c. simpl. now left.
  - intros. destruct c', c''. now left.
Defined.


Structure Instant {C : Set} `{Clockable C} : Set :=
  declare_Instant { src : C; num : nat }.

Definition timer_instant := @Instant unit unit_clockable.

Example e : timer_instant := {| src := tt; num := 3 |}.