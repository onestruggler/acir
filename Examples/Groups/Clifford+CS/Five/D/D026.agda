{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D026 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at0210243143 ; lem-box-tQ-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CSd14-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CS14-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CS04-CCZ123 ; lem-comm-CSd04-CCZ123)
-- F4-S1-K3: 1 steps
lem-F4-S1-K3 : Complete 4 → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S1-CS0: 15 steps
lem-F4-S1-CS0 : Complete 4 → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS14 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff213 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ X4 ∷ Toff213 ∷ []) (Toff213 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS14 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff213 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ X4 ∷ Toff213 ∷ []) (Toff213 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 3 (S1 ∷ CS14⁻ ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ X4 ∷ []) (S1 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CS14 ∷ X4 ∷ []) (lw0 c4 (S1 ∷ CS14⁻ ∷ []) (X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S1-CS1: 18 steps
lem-F4-S1-CS1 : Complete 4 → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-CS1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 4 (CCZ014 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS14 ∷ X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 2 (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 c4) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ S1 ∷ CS14⁻ ∷ [])
  b1 = at 2 3 (S1 ∷ CS14⁻ ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ X4 ∷ []) (S1 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CCZ014 ∷ S1 ∷ CS14⁻ ∷ []) (pw2 c4 (S1 ∷ CS14⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ S1 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 c4) ▸
       at 3 2 (Toff023 ∷ S1 ∷ []) (lw4 c4 (S1 ∷ Toff023 ∷ []) (Toff023 ∷ S1 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 6 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S1 ∷ CS14⁻ ∷ []) (lw0 c4 (S1 ∷ CS14⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S1 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ S1 ∷ CS14⁻ ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b2 = at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 2 (X4 ∷ CS14 ∷ X4 ∷ []) (lw0 c4 (S1 ∷ CS14⁻ ∷ []) (X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S1-CS2: 15 steps
lem-F4-S1-CS2 : Complete 4 → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS14 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff013 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS14 ∷ X4 ∷ Toff013 ∷ []) (Toff013 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS14 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff013 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS14 ∷ X4 ∷ Toff013 ∷ []) (Toff013 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (S1 ∷ CS14⁻ ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ X4 ∷ []) (S1 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CS14 ∷ X4 ∷ []) (lw0 c4 (S1 ∷ CS14⁻ ∷ []) (X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S2-I: 1 steps
lem-F4-S2-I : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S2-S0: 1 steps
lem-F4-S2-S0 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S2-S1: 1 steps
lem-F4-S2-S1 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S2-S2: 1 steps
lem-F4-S2-S2 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S2-S3: 1 steps
lem-F4-S2-S3 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S2-K0: 1 steps
lem-F4-S2-K0 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S2-K1: 1 steps
lem-F4-S2-K1 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S2-K2: 1 steps
lem-F4-S2-K2 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S2-K3: 1 steps
lem-F4-S2-K3 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- CSdu-box-2 @0210243143: 17 steps
lem-CSdu-box-2-at0210243143 : Complete 4 → ⟪ (CS24⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS24⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS24⁻ ∷ Bx2-0413 ∷ []) (Toff204 ∷ CS24⁻ ∷ CS04⁻ ∷ CCZ123 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ Toff204 ∷ CCZ123 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (Toff204 ∷ CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CS24⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (pw3 c4 (CCZ024 ∷ []) (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ123 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ123 ∷ CX20 ∷ []) (lw4 c4 (CX20 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 c4) ▸
       at 4 2 (CCZ123 ∷ CX20 ∷ []) (lw4 c4 (CX20 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 c4) ▸ done

  b1 : Chain (Toff204 ∷ CS24⁻ ∷ CS04⁻ ∷ CCZ123 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ Toff204 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CS24⁻ ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (pw3 c4 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 c4) ▸
       at 1 2 (CCZ123 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ Toff204 ∷ []) (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff204 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff204 ∷ CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CS24⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ CS04⁻ ∷ CZ04 ∷ CCZ024 ∷ []) (CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CS24⁻ ∷ []) (Bx2-0413 ∷ CS24⁻ ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸ done


-- Su-box @0210243143: 17 steps
lem-Su-box-at0210243143 : Complete 4 → ⟪ (S2 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ S2 ∷ []) ⟫ʷ
lem-Su-box-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (S2 ∷ Bx2-0413 ∷ []) (Toff204 ∷ S2 ∷ CS04 ∷ CCZ123 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ Toff204 ∷ CCZ123 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (Toff204 ∷ S2 ∷ CS04 ∷ CCZ024 ∷ []) (pw1 c4 (S2 ∷ Toff204 ∷ []) (Toff204 ∷ S2 ∷ CS04 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (pw3 c4 (CCZ024 ∷ []) (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ123 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ123 ∷ CX20 ∷ []) (lw4 c4 (CX20 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 c4) ▸
       at 4 2 (CCZ123 ∷ CX20 ∷ []) (lw4 c4 (CX20 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 c4) ▸ done

  b1 : Chain (Toff204 ∷ S2 ∷ CS04 ∷ CCZ123 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ Toff204 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ S2 ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (pw3 c4 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 c4) ▸
       at 1 2 (CCZ123 ∷ S2 ∷ []) (lw4 c4 (S2 ∷ CCZ123 ∷ []) (CCZ123 ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ Toff204 ∷ []) (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff204 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ Toff204 ∷ []) (Toff204 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff204 ∷ S2 ∷ CS04 ∷ CCZ024 ∷ []) (pw1 c4 (S2 ∷ Toff204 ∷ []) (Toff204 ∷ S2 ∷ CS04 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (S2 ∷ []) (pw1 c4 (S2 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) (S2 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ S2 ∷ []) (lw4 c4 (S2 ∷ CCZ123 ∷ []) (CCZ123 ∷ S2 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ S2 ∷ []) (Bx2-0413 ∷ S2 ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸ done


-- XCSX-box-2 @0210243143: 4 steps
lem-XCSX-box-2-at0210243143 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-2-at0210243143 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 3 (S2 ∷ CS24⁻ ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ []) (S2 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ CS24⁻ ∷ []) (lem-CSdu-box-2-at0210243143 c4) ▸
       at 0 2 (Bx2-0413 ∷ S2 ∷ []) (lem-Su-box-at0210243143 c4) ▸
       at 1 2 (X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (S2 ∷ CS24⁻ ∷ []) (X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

