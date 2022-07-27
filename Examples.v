Require Import Utf8.
Require Import ClockStructs.Preliminaries.
Require Import ClockStructs.Concepts.
Require Import Coq.Arith.PeanoNat.


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
      destruct x as [sx nx], y as [sy ny].
      destruct sx, sy.
      compute in H1. compute in H2.
      assert (H3 : (let (x, _) := ny in x) ≤ S (let (x, _) := ny in x)). {
        apply le_S. apply le_n. }
      assert (H4 : S (let (x, _) := nx in x) ≤ S (let (x, _) := ny in x)). {
        now apply Nat.le_trans with (let (x, _) := ny in x). }
      assert (H5 : S (let (x, _) := nx in x) ≤ (let (x, _) := nx in x)). {
        now apply Nat.le_trans with (S (let (x, _) := ny in x)). }
      now apply Nat.lt_irrefl with (let (x, _) := nx in x).
    + unfold Transitive. intros * H1 H2.
      destruct x as [sx nx], y as [sy ny], z as [sz nz].
      compute in H1. compute in H2. compute.
      now apply Nat.lt_trans with (let (x, _) := ny in x).
  - constructor. 
    + unfold Reflexive. intro. destruct x as [sx nx]. now compute.
    + unfold Symmetric. intros. destruct x as [sx nx], y as [sy ny].
      compute. compute in H. now rewrite H.
    + unfold Transitive. intros * H1 H2.
      destruct x as [sx nx], y as [sy ny], z as [sz nz].
      compute. compute in H1. compute in H2. now rewrite H1.
  - intros * H1 H2 H3.
    destruct i as [si ni], i' as [si' ni'], j as [sj nj], j' as [sj' nj'].
    compute. compute in H1. compute in H2. compute in H3.
    rewrite <- H1. now rewrite <- H2.
  - intros * H1. split; intro H2; destruct i as [si ni], j as [sj nj];
      compute; compute in H1; now compute in H2.
  - intro. exists (S (number i)). intros * H.
    destruct i as [si ni], j as [sj nj]. compute. compute in H.
    now apply le_S in H.
Defined.

Definition timer : ClockStruct unit timer_prec timer_sync.
Proof. exact cert_timer. Defined.
