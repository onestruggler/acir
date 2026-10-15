{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D032 where

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
open import Examples.Groups.Clifford+CS.Five.D.D031 using (lem-QVQ-at12233441 ; lem-box-perm-1324-at122441 ; lem-tP-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CS04-CCZ123 ; lem-comm-CSd04-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-comm-CK41-CCZ023)
-- box-cP @12233441: 12 steps
lem-box-cP-at12233441 : Complete 4 → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-box-cP-at12233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2341 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (pw3 c4 (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (pw3 c4 (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-QVQ-at12233441 c4) ▸
       at 1 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at12233441 c4) ▸
       at 2 2 [] (lw4 c4 (Toff023 ∷ Toff023 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4-K1-CS2: 19 steps
lem-F4-K1-CS2 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-CS2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ023 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 3 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 2 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 1 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 c4) ▸
       at 0 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (CCZ023 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ []) (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 c4) ▸
       at 2 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 4 (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ []) (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 0 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4-K2-I: 1 steps
lem-F4-K2-I : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K2-S0: 1 steps
lem-F4-K2-S0 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K2-S1: 1 steps
lem-F4-K2-S1 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K2-S2: 1 steps
lem-F4-K2-S2 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K2-S3: 1 steps
lem-F4-K2-S3 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K2-K0: 1 steps
lem-F4-K2-K0 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K2-K1: 1 steps
lem-F4-K2-K1 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K2-K2: 1 steps
lem-F4-K2-K2 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K2-K3: 1 steps
lem-F4-K2-K3 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- CSu-box-2 @0210243143: 17 steps
lem-CSu-box-2-at0210243143 : Complete 4 → ⟪ (CS24 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS24 ∷ []) ⟫ʷ
lem-CSu-box-2-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS24 ∷ Bx2-0413 ∷ []) (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ123 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ Toff204 ∷ CCZ123 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ024 ∷ []) (pw1 c4 (CS24 ∷ Toff204 ∷ []) (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (pw3 c4 (CCZ024 ∷ []) (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ123 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ123 ∷ CX20 ∷ []) (lw4 c4 (CX20 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 c4) ▸
       at 4 2 (CCZ123 ∷ CX20 ∷ []) (lw4 c4 (CX20 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 c4) ▸ done

  b1 : Chain (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ123 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ Toff204 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CS24 ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (pw3 c4 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 c4) ▸
       at 1 2 (CCZ123 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ Toff204 ∷ []) (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff204 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ Toff204 ∷ []) (Toff204 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ024 ∷ []) (pw1 c4 (CS24 ∷ Toff204 ∷ []) (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (CS24 ∷ []) (pw1 c4 (CS24 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) (CS24 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CS24 ∷ []) (Bx2-0413 ∷ CS24 ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸ done


-- Ku-box @0210243143: 6 steps
lem-Ku-box-at0210243143 : Complete 4 → ⟪ (K2 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ K2 ∷ []) ⟫ʷ
lem-Ku-box-at0210243143 c4 = run b0
  where
  b0 : Chain (K2 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ K2 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ K2 ∷ []) (pw1 c4 (K2 ∷ Toff204 ∷ []) (CCZ024 ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ K2 ∷ []) (lw4 c4 (K2 ∷ CCZ123 ∷ []) (Toff213 ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ K2 ∷ []) (pw1 c4 (K2 ∷ Toff204 ∷ []) (CCZ024 ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ K2 ∷ []) (lw4 c4 (K2 ∷ CCZ123 ∷ []) (Toff213 ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done


-- Kdu-box @0210243143: 6 steps
lem-Kdu-box-at0210243143 : Complete 4 → ⟪ (K2⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ K2⁻ ∷ []) ⟫ʷ
lem-Kdu-box-at0210243143 c4 = run b0
  where
  b0 : Chain (K2⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ K2⁻ ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ K2⁻ ∷ []) (pw1 c4 (K2⁻ ∷ Toff204 ∷ []) (CCZ024 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ K2⁻ ∷ []) (lw4 c4 (K2⁻ ∷ CCZ123 ∷ []) (Toff213 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ K2⁻ ∷ []) (pw1 c4 (K2⁻ ∷ Toff204 ∷ []) (CCZ024 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ K2⁻ ∷ []) (lw4 c4 (K2⁻ ∷ CCZ123 ∷ []) (Toff213 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done


-- CKdu-box-2 @0210243143: 7 steps
lem-CKdu-box-2-at0210243143 : Complete 4 → ⟪ (CK42⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CK42⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2-at0210243143 c4 = run b0
  where
  b0 : Chain (CK42⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CK42⁻ ∷ [])
  b0 = at 0 1 (CS24 ∷ K2⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (lw0 c4 (CK42⁻ ∷ []) (CS24 ∷ K2⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx2-0413 ∷ CS24 ∷ []) (lem-CSu-box-2-at0210243143 c4) ▸
       at 3 2 (Bx2-0413 ∷ K2 ∷ []) (lem-Ku-box-at0210243143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CS24 ∷ []) (lem-CSu-box-2-at0210243143 c4) ▸
       at 1 2 (Bx2-0413 ∷ K2⁻ ∷ []) (lem-Kdu-box-at0210243143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CS24 ∷ []) (lem-CSu-box-2-at0210243143 c4) ▸
       at 1 5 (CK42⁻ ∷ []) (lw0 c4 (CS24 ∷ K2⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (CK42⁻ ∷ []) tt tt Eq.refl) ▸ done


-- XCKX-box-2 @0210243143: 4 steps
lem-XCKX-box-2-at0210243143 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-2-at0210243143 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 3 (K2 ∷ CK42⁻ ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ []) (K2 ∷ CK42⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ CK42⁻ ∷ []) (lem-CKdu-box-2-at0210243143 c4) ▸
       at 0 2 (Bx2-0413 ∷ K2 ∷ []) (lem-Ku-box-at0210243143 c4) ▸
       at 1 2 (X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (K2 ∷ CK42⁻ ∷ []) (X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

