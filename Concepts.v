Require Import Utf8.
Require Import ClockStructs.Preliminaries.


Record Instant {clock : Set} : Set :=
  define_Instant { source : clock; number : posnat }. 

Class ClockStruct (clock : Set) (prec sync : @relation (@Instant clock)) :=
{ clock_tfinConstr : TFinite clock
; clock_decConstr : ∀ c' c'' : clock, {c' = c''} + {c' ≠ c''}
; prec_soConstr : StrictOrder prec
; sync_eqConstr : Equivalence sync
; sync_prec_congConstr : ∀ i i' j j' : Instant,
    sync i i' → sync j j' → prec i j → prec i' j' 
; clocklinConstr : ∀ i j : Instant,
    source i = source j → (prec i j ↔ number i < number j)
; fin_causalityConstr :
     ∀ i : Instant, EFinite (inverse_image prec i)
}.

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