{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D204 where

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
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-beta-T-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D181 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2442)
-- F4 CS13^0|S1^1: 58 steps
lem-F4-CS13ᵖ0∣S1ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS13ᵖ0∣S1ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ CS14 ∷ []) (X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS12⁻ ∷ []) (refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b1 = at 9 4 (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 6 4 (CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 3 4 (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b3 = at 15 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b4 = at 6 4 (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b5 = at 9 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b6 = at 0 4 (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 2 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸
       at 3 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b7 : Chain (CS14 ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ [])
  b7 = at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- F4 CS13^0|S2^1: 30 steps
lem-F4-CS13ᵖ0∣S2ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS13ᵖ0∣S2ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ CS24 ∷ []) (X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS12⁻ ∷ []) (refl) ▸
       at 12 4 (CS24 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b1 = at 9 4 (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 6 4 (CS24 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 3 4 (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CS24 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CS24 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (CS24 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (CS24 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b3 : Chain (CS24 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸
       at 3 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- F4 CS13^0|S3^1: 30 steps
lem-F4-CS13ᵖ0∣S3ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS13ᵖ0∣S3ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ CS34 ∷ []) (X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS12⁻ ∷ []) (refl) ▸
       at 12 4 (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b1 = at 9 4 (CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 6 4 (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 3 4 (CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b3 : Chain (CS34 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸
       at 3 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- F4 CS13^0|K0^1: 131 steps
lem-F4-CS13ᵖ0∣K0ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS13ᵖ0∣K0ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ CK40 ∷ []) (ι ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b0 = at 3 1 (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (pw1 c4 (CK40 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb0-1-43-2 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b1 = at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS12⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS12 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b2 = at 4 4 (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b3 = at 1 4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b4 = at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 5 (Sb0-1-43-2 ∷ []) (refl) ▸
       at 3 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (CS12⁻ ∷ []) (refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b5 = at 14 4 (CS04 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 11 4 (CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS12 ∷ []) (refl) ▸
       at 8 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 5 4 (CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b6 = at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b7 = at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b8 = at 5 2 (K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ []) (K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K0 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2442 c4) ▸
       at 3 2 (K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ []) (K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K0 ∷ CS04 ∷ [])
  b9 = at 17 1 (CS12⁻ ∷ []) (refl) ▸
       at 16 4 (CS04 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 13 4 (CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS12 ∷ []) (refl) ▸
       at 10 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 7 4 (CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K0 ∷ CS04 ∷ [])
  b10 = at 5 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K0 ∷ CS04 ∷ [])
  b11 = at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS04 ∷ [])
  b12 = at 6 5 (Sb0-1-43-2 ∷ []) (refl) ▸
       at 7 2 (K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ []) (K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K0 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2442 c4) ▸
       at 5 2 (K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ []) (K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b13 = at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (CS12⁻ ∷ []) (refl) ▸
       at 18 4 (CS04 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 15 4 (CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS12 ∷ []) (refl) ▸
       at 12 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b14 = at 9 4 (CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b15 = at 6 4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (CK40 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ [])
  b16 = at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 5 (Sb0-1-43-2 ∷ []) (refl) ▸
       at 0 7 (CK40 ∷ []) (pw1 c4 (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (CK40 ∷ []) tt tt Eq.refl) ▸ done


-- F4 CS13^0|K1^1: 221 steps
lem-F4-CS13ᵖ0∣K1ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS13ᵖ0∣K1ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (run b27)))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ CK41 ∷ []) (ι ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b0 = at 3 1 (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (pw0 c4 (CK41 ∷ []) (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb0-1-43-2 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b1 = at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS12⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS12 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b2 = at 9 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b3 = at 4 4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b4 = at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 5 (Sb0-1-43-2 ∷ []) (refl) ▸
       at 3 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b5 = at 15 1 (CS12⁻ ∷ []) (refl) ▸
       at 14 4 (CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 11 4 (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS12 ∷ []) (refl) ▸
       at 8 4 (CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 5 4 (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ CS03 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b6 = at 3 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ CS03 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b7 = at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ CS03 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b8 = at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ CS03 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b9 = at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b10 = at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b11 = at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-43-2 ∷ []) (refl) ▸
       at 4 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ [])
  b12 = at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (CS12 ∷ []) (refl) ▸
       at 16 1 (CS12⁻ ∷ []) (refl) ▸
       at 9 12 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 19 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 6 6 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ [])
  b13 = at 4 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ [])
  b14 = at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ [])
  b15 = at 13 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 15 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ [])
  b16 = at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 9 6 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 7 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 8 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CS02 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ [])
  b17 = at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b18 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CS02 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ [])
  b18 = at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 9 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 3 6 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b19 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ [])
  b19 = at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b20 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ [])
  b20 = at 7 5 (Sb0-1-43-2 ∷ []) (refl) ▸
       at 7 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (CS12⁻ ∷ []) (refl) ▸
       at 18 4 (CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b21 = at 20 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 15 4 (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS12 ∷ []) (refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 9 4 (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b22 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b22 = at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b23 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b23 = at 24 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b24 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b24 = at 17 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b25 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b25 = at 18 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b26 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ [])
  b26 = at 11 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b27 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ [])
  b27 = at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 5 (Sb0-1-43-2 ∷ []) (refl) ▸
       at 0 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 0 7 (CK41 ∷ []) (pw0 c4 (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (CK41 ∷ []) tt tt Eq.refl) ▸ done

