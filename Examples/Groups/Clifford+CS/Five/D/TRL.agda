------------------------------------------------------------------------
-- Presentations of groups
--
-- The two-wire λ-images of Five.D.TR
--
-- The derivations that Five.D.TR needs (its `ok₂` and lem-calc-x4x4),
-- apart from the de-borrowing's, which import TR.  Written by
-- `scratchpad/five/trsplit5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.TRL where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0283 ; wl0900 ; wl0901 ; wl0904 ; wl0907 ; wl0910 ; wl0913 ; wp0470 ; wp0471 ; wp0472 ; wp0473 ; wp0474 ; wp0475 ; wp0480 ; wp0481 ; wp0482)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-F1-comm-CS-S0 ; lem-F1-comm-CS-S1 ; lem-F1-order-CS)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F1-X-CS0 ; lem-F1-X-CS1)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-F1-CS-K0)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-F1-CS-K1)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-F2-iI∣CS01)
-- tr order-I at 0: 1 steps
lem-tr-order-I-at-0 : Ws → ⟪ (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-I-at-0 c4 = run b0
  where
  b0 : Chain (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) []
  b0 = at 0 4 [] (wl0900 (lit c4)) ▸ done


-- tr order-I at 1: 1 steps
lem-tr-order-I-at-1 : Ws → ⟪ (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-I-at-1 c4 = run b0
  where
  b0 : Chain (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) []
  b0 = at 0 4 [] (wl0900 (lit c4)) ▸ done


-- tr order-I at 2: 1 steps
lem-tr-order-I-at-2 : Ws → ⟪ (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-I-at-2 c4 = run b0
  where
  b0 : Chain (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) []
  b0 = at 0 4 [] (wl0900 (lit c4)) ▸ done


-- tr order-S at 0: 1 steps
lem-tr-order-S-at-0 : Ws → ⟪ (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-S-at-0 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) []
  b0 = at 0 4 [] (wp0470 c4) ▸ done


-- tr order-S at 1: 1 steps
lem-tr-order-S-at-1 : Ws → ⟪ (CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-S-at-1 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) []
  b0 = at 0 4 [] (wl0901 (lit c4)) ▸ done


-- tr order-K at 0: 1 steps
lem-tr-order-K-at-0 : Ws → ⟪ (CK40 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-tr-order-K-at-0 c4 = run b0
  where
  b0 : Chain (CK40 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 2 (S4 ∷ S4 ∷ S4 ∷ []) (wp0471 c4) ▸ done


-- tr order-K at 1: 1 steps
lem-tr-order-K-at-1 : Ws → ⟪ (CK41 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-tr-order-K-at-1 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 2 (S4 ∷ S4 ∷ S4 ∷ []) (wl0904 (lit c4)) ▸ done


-- tr order-SK at 0: 1 steps
lem-tr-order-SK-at-0 : Ws → ⟪ (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-tr-order-SK-at-0 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 6 (S4 ∷ S4 ∷ S4 ∷ []) (wp0472 c4) ▸ done


-- tr order-SK at 1: 1 steps
lem-tr-order-SK-at-1 : Ws → ⟪ (CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-tr-order-SK-at-1 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 6 (S4 ∷ S4 ∷ S4 ∷ []) (wl0907 (lit c4)) ▸ done


-- tr order-CS at 0: 1 steps
lem-tr-order-CS-at-0 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-tr-order-CS-at-0 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) []
  b0 = at 0 4 [] (lem-F1-order-CS c4) ▸ done


-- tr comm-CS-S0 at 0: 1 steps
lem-tr-comm-CS-S0-at-0 : Ws → ⟪ (Sb2-0-41-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-tr-comm-CS-S0-at-0 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CS04 ∷ []) (CS04 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 2 (CS04 ∷ Sb2-0-41-3 ∷ []) (lem-F1-comm-CS-S0 c4) ▸ done


-- tr comm-CS-S1 at 0: 1 steps
lem-tr-comm-CS-S1-at-0 : Ws → ⟪ (Sb2-0-41-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-tr-comm-CS-S1-at-0 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CS14 ∷ []) (CS14 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 2 (CS14 ∷ Sb2-0-41-3 ∷ []) (lem-F1-comm-CS-S1 c4) ▸ done


-- tr X-CS0 at 0: 1 steps
lem-tr-X-CS0-at-0 : Ws → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-tr-X-CS0-at-0 c4 = run b0
  where
  b0 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b0 = at 0 6 (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (lem-F1-X-CS0 c4) ▸ done


-- tr X-CS1 at 0: 1 steps
lem-tr-X-CS1-at-0 : Ws → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-tr-X-CS1-at-0 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b0 = at 0 6 (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (lem-F1-X-CS1 c4) ▸ done


-- tr CS-K0 at 0: 1 steps
lem-tr-CS-K0-at-0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-tr-CS-K0-at-0 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 5 (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0 c4) ▸ done


-- tr CS-K1 at 0: 1 steps
lem-tr-CS-K1-at-0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-tr-CS-K1-at-0 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 5 (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K1 c4) ▸ done


-- tr comm1 S I at 0: 1 steps
lem-tr-comm1-S-I-at-0 : Ws → ⟪ (S4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-S-I-at-0 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS04 ∷ []) (CS04 ∷ S4 ∷ [])
  b0 = at 0 2 (CS04 ∷ S4 ∷ []) (sym (wp0473 c4)) ▸ done


-- tr comm1 S S0 at 0: 1 steps
lem-tr-comm1-S-S0-at-0 : Ws → ⟪ (CS14 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CS14 ∷ []) ⟫ʷ
lem-tr-comm1-S-S0-at-0 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CS04 ∷ []) (CS04 ∷ CS14 ∷ [])
  b0 = at 0 2 (CS04 ∷ CS14 ∷ []) (sym (wp0474 c4)) ▸ done


-- tr comm1 S K0 at 0: 1 steps
lem-tr-comm1-S-K0-at-0 : Ws → ⟪ (CK41 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK41 ∷ []) ⟫ʷ
lem-tr-comm1-S-K0-at-0 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CS04 ∷ []) (CS04 ∷ CK41 ∷ [])
  b0 = at 0 2 (CS04 ∷ CK41 ∷ []) (wp0475 c4) ▸ done


-- tr comm1 K I at 0: 1 steps
lem-tr-comm1-K-I-at-0 : Ws → ⟪ (S4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-K-I-at-0 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK40 ∷ []) (CK40 ∷ S4 ∷ [])
  b0 = at 0 2 (CK40 ∷ S4 ∷ []) (sym (wp0480 c4)) ▸ done


-- tr comm1 K S0 at 0: 1 steps
lem-tr-comm1-K-S0-at-0 : Ws → ⟪ (CS14 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS14 ∷ []) ⟫ʷ
lem-tr-comm1-K-S0-at-0 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CK40 ∷ []) (CK40 ∷ CS14 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS14 ∷ []) (sym (wp0481 c4)) ▸ done


-- tr comm1 K K0 at 0: 1 steps
lem-tr-comm1-K-K0-at-0 : Ws → ⟪ (CK41 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CK41 ∷ []) ⟫ʷ
lem-tr-comm1-K-K0-at-0 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CK40 ∷ []) (CK40 ∷ CK41 ∷ [])
  b0 = at 0 2 (CK40 ∷ CK41 ∷ []) (sym (wp0482 c4)) ▸ done


-- tr comm1 S I at 1: 1 steps
lem-tr-comm1-S-I-at-1 : Ws → ⟪ (S4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-S-I-at-1 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS14 ∷ []) (CS14 ∷ S4 ∷ [])
  b0 = at 0 2 (CS14 ∷ S4 ∷ []) (sym (wl0910 (lit c4))) ▸ done


-- tr comm1 K I at 1: 1 steps
lem-tr-comm1-K-I-at-1 : Ws → ⟪ (S4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-K-I-at-1 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK41 ∷ []) (CK41 ∷ S4 ∷ [])
  b0 = at 0 2 (CK41 ∷ S4 ∷ []) (sym (wl0913 (lit c4))) ▸ done


-- tr comm2 I at 0: 1 steps
lem-tr-comm2-I-at-0 : Ws → ⟪ (S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm2-I-at-0 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ S4 ∷ []) (lem-F2-iI∣CS01 c4) ▸ done


-- calc x4x4: 1 steps
lem-calc-x4x4 : Ws → ⟪ (X4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-calc-x4x4 c4 = run b0
  where
  b0 : Chain (X4 ∷ X4 ∷ []) []
  b0 = at 0 2 [] (wl0283 (lit c4)) ▸ done


