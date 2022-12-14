Require Import Utf8.
Require Import ClockStructs.Preliminaries.


Record Instant {clock : Set} : Set := define_Instant
{ source : clock
; number : posnat }. 

Class ClockStruct (clock : Set) (prec sync : @relation (@Instant clock)) :=
{ clock_Fin_constr : Finite clock
; clock_dec_constr : ∀ c' c'' : clock, {c' = c''} + {c' ≠ c''}
; prec_strict_order_constr : StrictOrder prec
; sync_equiv_constr : Equivalence sync
; sync_prec_congruence_constr : ∀ i i' j j' : Instant,
    sync i i' → sync j j' → prec i j → prec i' j' 
; prec_on_clockline_constr : ∀ i j : Instant,
    source i = source j → (prec i j ↔ number i < number j)
; fin_causality :
    ∀ i : Instant, ∃ n : nat, ∀ j : Instant, prec j i → number j < n }.

Structure clock_struct := define_clock_struct
{ clock : Set
; instant := @Instant clock
; prec : @relation instant
; sync : @relation instant
; cert_ClockStruct : ClockStruct clock prec sync }.


Class ClockMorphism (dom cod : clock_struct)
                    (map : instant dom → instant cod) :=
{ clock_inv : ∀ i j : instant dom,
    source i = source j → source (map i) = source (map j)
; prec_inv : ∀ i j : instant dom, prec dom i j → prec cod (map i) (map j)
; sync_inv : ∀ i j : instant dom, sync dom i j → sync cod (map i) (map j)
}.

Structure clock_morphism := define_clock_morphism
{ dom : clock_struct
; cod : clock_struct
; map : instant dom → instant cod
; cert_ClockMorphism : ClockMorphism dom cod map
}.