Require Import Utf8.
Require Import ClockStructs.Preliminaries.
Require Import ClockStructs.Concepts.


(* Timer system *)
Definition timerInstant := @Instant unit.

Definition timer_prec := fun i j : timerInstant => number i < number j.
Definition timer_sync := fun i j : timerInstant => number i = number j.

Instance cert_timer : ClockStruct unit timer_prec timer_sync.
Proof.
  constructor.
  - exact unit_fin_cert.
  - intros. destruct c', c''. now left.
  - constructor.
    + unfold Asymmetric. intros * H1 H2.
      destruct x, y.
      compute in H1. compute in H2.