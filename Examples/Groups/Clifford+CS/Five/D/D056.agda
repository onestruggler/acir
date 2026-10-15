{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D056 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CX24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-comm-CCZ024-CX13)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-comm-CCZ024-CX31)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-comm-TOFF013-CX24)
-- F4-CS2-CS2: 286 steps
lem-F4-CS2-CS2 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-CS2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (lw4 c4 (CZ02 ∷ Toff013 ∷ []) (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 6 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 8 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CZ02 ∷ []) (pw3 c4 (CZ02 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (lw3 c4 (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CCZ024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 6 2 (Toff013 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff013 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (pw3 c4 (K1⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (pw3 c4 (K1 ∷ CCZ024 ∷ []) (CCZ024 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ Toff013 ∷ []) (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b5 = at 13 2 (CCZ024 ∷ K1⁻ ∷ []) (pw3 c4 (K1⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 10 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ K1 ∷ []) (pw3 c4 (K1 ∷ CCZ024 ∷ []) (CCZ024 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 8 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b6 = at 6 2 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (pw1 c4 (Toff034 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ Toff013 ∷ []) (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Toff013 ∷ CS23 ∷ []) (lw4 c4 (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 c4) ▸
       at 10 2 (Toff013 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 c4) ▸
       at 8 2 (Toff013 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b7 = at 9 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff013 ∷ Toff034 ∷ []) (pw2 c4 (Toff034 ∷ Toff013 ∷ []) (Toff013 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CCZ234 ∷ []) (pw1 c4 (Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 3 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b8 = at 5 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff013 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ K1⁻ ∷ []) (pw3 c4 (K1⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸ done

  b9 : Chain (X4 ∷ Bx0-2431 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b9 = at 5 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 3 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ K1 ∷ []) (pw3 c4 (K1 ∷ CCZ024 ∷ []) (CCZ024 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 3 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ Toff013 ∷ []) (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ024 ∷ K1⁻ ∷ []) (pw3 c4 (K1⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b10 = at 10 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 8 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ K1 ∷ []) (pw3 c4 (K1 ∷ CCZ024 ∷ []) (CCZ024 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (pw1 c4 (Toff034 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b11 = at 7 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ Toff013 ∷ []) (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff013 ∷ CS23 ∷ []) (lw4 c4 (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 c4) ▸
       at 8 2 (Toff013 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 c4) ▸
       at 6 2 (Toff013 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Bx0-2431 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b12 = at 5 2 (Toff013 ∷ Toff034 ∷ []) (pw2 c4 (Toff034 ∷ Toff013 ∷ []) (Toff013 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ234 ∷ []) (pw1 c4 (Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (lw4 c4 (CZ02 ∷ Toff013 ∷ []) (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Bx0-2431 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Bx0-2431 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b13 = at 8 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (pw3 c4 (CZ02 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Bx0-2431 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b14 = at 3 3 (X4 ∷ []) (lw3 c4 (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸ done

  b15 : Chain (Bx0-2431 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b15 = at 4 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 3 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸ done

  b16 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ Bx0-2431 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b16 = at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 8 (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸ done

  b17 : Chain (Bx0-2431 ∷ X4 ∷ Bx0-2431 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b17 = at 3 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ Toff134 ∷ CS12 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 2 (CX31 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸ done

  b18 : Chain (Bx0-2431 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b18 = at 6 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 6 (CX31 ∷ Toff134 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX31 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CX30 ∷ CX31 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX31 ∷ []) (CX30 ∷ CX31 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ Toff134 ∷ []) (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX30 ∷ CCZ234 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CX30 ∷ []) (CX30 ∷ CCZ234 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 c4) ▸
       at 7 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b19 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b19 = at 10 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K1 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 12 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 14 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K1⁻ ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b20 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b20 = at 9 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX30 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX30 ∷ []) (CX30 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ CS34 ∷ []) (CS34 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 c4) ▸
       at 6 2 (CS34⁻ ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 c4) ▸
       at 8 2 (CS23 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS23 ∷ []) (CS23 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CCZ234 ∷ CX30 ∷ CX31 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ Toff013 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b21 = at 4 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX30 ∷ CX31 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX31 ∷ []) (CX30 ∷ CX31 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff034 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ Toff034 ∷ []) (Toff034 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS34 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ CS34 ∷ []) (CS34 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 c4) ▸
       at 10 2 (CS34⁻ ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 c4) ▸ done

  b22 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CCZ234 ∷ CX30 ∷ CX31 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ Toff013 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CX31 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b22 = at 12 2 (CS23 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS23 ∷ []) (CS23 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 8 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ Toff134 ∷ []) (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CCZ234 ∷ []) (pw1 c4 (CX30 ∷ CCZ234 ∷ CX30 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ234 ∷ []) (pw1 c4 (Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (CX31 ∷ Toff134 ∷ []) (lw0 c4 (CCZ234 ∷ CX31 ∷ CCZ234 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 c4) ▸
       at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸ done

  b23 : Chain (Bx0-2431 ∷ X4 ∷ CX31 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CX31 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b23 = at 3 2 (K1 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 6 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 8 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K1⁻ ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸ done

  b24 : Chain (Bx0-2431 ∷ X4 ∷ CX31 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS12 ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b24 = at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸ done

  b25 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS12 ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b25 = at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 5 (CS12 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS12 ∷ []) (CS12 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (CS12 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS12 ∷ []) (CS12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS12 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS12 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS12 ∷ []) (CS12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS12 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b26 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ [])
  b26 = at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX31 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (CS12 ∷ []) (refl) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b27 = at 5 6 (CX31 ∷ Toff134 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX31 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (CX30 ∷ CX31 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX31 ∷ []) (CX30 ∷ CX31 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ Toff134 ∷ []) (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX30 ∷ CCZ234 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CX30 ∷ []) (CX30 ∷ CCZ234 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 c4) ▸
       at 9 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸ done

  b28 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b28 = at 11 2 (K1 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 14 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 16 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1⁻ ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 11 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸ done

  b29 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CCZ234 ∷ Toff013 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b29 = at 5 2 (CX30 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX30 ∷ []) (CX30 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS34 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ CS34 ∷ []) (CS34 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 c4) ▸
       at 8 2 (CS34⁻ ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 c4) ▸
       at 10 2 (CS23 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS23 ∷ []) (CS23 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done

  b30 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CCZ234 ∷ Toff013 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CCZ234 ∷ CX30 ∷ CX31 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b30 = at 7 2 (CX30 ∷ CX31 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX31 ∷ []) (CX30 ∷ CX31 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff034 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ Toff034 ∷ []) (Toff034 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CS34 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ CS34 ∷ []) (CS34 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 c4) ▸
       at 12 2 (CS34⁻ ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 c4) ▸
       at 14 2 (CS23 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS23 ∷ []) (CS23 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b31 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CCZ234 ∷ CX30 ∷ CX31 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b31 = at 10 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ Toff134 ∷ []) (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ234 ∷ []) (pw1 c4 (CX30 ∷ CCZ234 ∷ CX30 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CCZ234 ∷ []) (pw1 c4 (Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CX31 ∷ Toff134 ∷ []) (lw0 c4 (CCZ234 ∷ CX31 ∷ CCZ234 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b32 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ Toff134 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b32 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b33 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ Toff134 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS12⁻ ∷ X4 ∷ [])
  b33 = at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 3 (Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS12⁻ ∷ X4 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b34 = at 6 5 (CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS12⁻ ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS12⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS12⁻ ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b35 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b35 = at 10 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F2-I-S0: 1 steps
lem-F2-I-S0 : Complete 4 → ⟪ (S4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S0 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS04 ∷ []) (CS04 ∷ S4 ∷ [])
  b0 = at 0 2 (CS04 ∷ S4 ∷ []) (pw1 c4 (S4 ∷ CS04 ∷ []) (CS04 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- F2-I-S1: 1 steps
lem-F2-I-S1 : Complete 4 → ⟪ (S4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S1 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS14 ∷ []) (CS14 ∷ S4 ∷ [])
  b0 = at 0 2 (CS14 ∷ S4 ∷ []) (lw0 c4 (S4 ∷ CS14 ∷ []) (CS14 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- F2-I-S2: 1 steps
lem-F2-I-S2 : Complete 4 → ⟪ (S4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S2 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS24 ∷ []) (CS24 ∷ S4 ∷ [])
  b0 = at 0 2 (CS24 ∷ S4 ∷ []) (lw0 c4 (S4 ∷ CS24 ∷ []) (CS24 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- F2-I-S3: 1 steps
lem-F2-I-S3 : Complete 4 → ⟪ (S4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S3 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS34 ∷ []) (CS34 ∷ S4 ∷ [])
  b0 = at 0 2 (CS34 ∷ S4 ∷ []) (lw0 c4 (S4 ∷ CS34 ∷ []) (CS34 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- F2-I-K0: 1 steps
lem-F2-I-K0 : Complete 4 → ⟪ (S4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K0 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK40 ∷ []) (CK40 ∷ S4 ∷ [])
  b0 = at 0 2 (CK40 ∷ S4 ∷ []) (pw1 c4 (S4 ∷ CK40 ∷ []) (CK40 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- F2-I-K1: 1 steps
lem-F2-I-K1 : Complete 4 → ⟪ (S4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K1 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK41 ∷ []) (CK41 ∷ S4 ∷ [])
  b0 = at 0 2 (CK41 ∷ S4 ∷ []) (lw0 c4 (S4 ∷ CK41 ∷ []) (CK41 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- F2-I-K2: 1 steps
lem-F2-I-K2 : Complete 4 → ⟪ (S4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K2 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK42 ∷ []) (CK42 ∷ S4 ∷ [])
  b0 = at 0 2 (CK42 ∷ S4 ∷ []) (lw0 c4 (S4 ∷ CK42 ∷ []) (CK42 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- F2-I-K3: 1 steps
lem-F2-I-K3 : Complete 4 → ⟪ (S4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K3 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK43 ∷ []) (CK43 ∷ S4 ∷ [])
  b0 = at 0 2 (CK43 ∷ S4 ∷ []) (lw0 c4 (S4 ∷ CK43 ∷ []) (CK43 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- F2-I-CS0: 13 steps
lem-F2-I-CS0 : Complete 4 → ⟪ (S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (S4 ∷ Sb2-0-41-3 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ S4 ∷ []) (pw1 c4 (S4 ∷ CCZ024 ∷ []) (CCZ024 ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ S4 ∷ []) (lw0 c4 (S4 ∷ Toff213 ∷ []) (Toff213 ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ S4 ∷ []) (pw1 c4 (S4 ∷ CCZ024 ∷ []) (CCZ024 ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ S4 ∷ []) (lw0 c4 (S4 ∷ Toff213 ∷ []) (Toff213 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Sb2-0-41-3 ∷ S4 ∷ [])
  b1 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 5 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S4 ∷ []) (pw2 c4 (S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F2-I-CS1: 13 steps
lem-F2-I-CS1 : Complete 4 → ⟪ (S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (S4 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ S4 ∷ []) (pw2 c4 (S4 ∷ CCZ014 ∷ []) (CCZ014 ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ S4 ∷ []) (pw1 c4 (S4 ∷ Toff023 ∷ []) (Toff023 ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ S4 ∷ []) (pw2 c4 (S4 ∷ CCZ014 ∷ []) (CCZ014 ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ S4 ∷ []) (pw1 c4 (S4 ∷ Toff023 ∷ []) (Toff023 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ S4 ∷ [])
  b1 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 5 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S4 ∷ []) (lw0 c4 (S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F2-I-CS2: 13 steps
lem-F2-I-CS2 : Complete 4 → ⟪ (S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (S4 ∷ Sb0-2-43-1 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ S4 ∷ []) (pw1 c4 (S4 ∷ CCZ024 ∷ []) (CCZ024 ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ S4 ∷ []) (pw2 c4 (S4 ∷ Toff013 ∷ []) (Toff013 ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ S4 ∷ []) (pw1 c4 (S4 ∷ CCZ024 ∷ []) (CCZ024 ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ S4 ∷ []) (pw2 c4 (S4 ∷ Toff013 ∷ []) (Toff013 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Sb0-2-43-1 ∷ S4 ∷ [])
  b1 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 5 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S4 ∷ []) (lw0 c4 (S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F2-S0-S1: 1 steps
lem-F2-S0-S1 : Complete 4 → ⟪ (CS04 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-S1 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CS14 ∷ []) (CS14 ∷ CS04 ∷ [])
  b0 = at 0 2 (CS14 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CS14 ∷ []) (CS14 ∷ CS04 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S0-S2: 1 steps
lem-F2-S0-S2 : Complete 4 → ⟪ (CS04 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-S2 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CS24 ∷ []) (CS24 ∷ CS04 ∷ [])
  b0 = at 0 2 (CS24 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CS24 ∷ []) (CS24 ∷ CS04 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S0-S3: 1 steps
lem-F2-S0-S3 : Complete 4 → ⟪ (CS04 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-S3 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CS34 ∷ []) (CS34 ∷ CS04 ∷ [])
  b0 = at 0 2 (CS34 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CS34 ∷ []) (CS34 ∷ CS04 ∷ []) tt tt Eq.refl) ▸ done


-- F2-S0-K1: 1 steps
lem-F2-S0-K1 : Complete 4 → ⟪ (CS04 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-K1 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CK41 ∷ []) (CK41 ∷ CS04 ∷ [])
  b0 = at 0 2 (CK41 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CK41 ∷ []) (CK41 ∷ CS04 ∷ []) tt tt Eq.refl) ▸ done

