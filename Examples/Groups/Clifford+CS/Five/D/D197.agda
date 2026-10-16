{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D197 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at0314203142)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F0)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-beta-T-at233442 ; lem-sym23-at233442 ; lem-sym23-at2442 ; lem-sym34-at243243 ; lem-sym34-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-sym12-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-auto-CCZ012-∣-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.D176 using (lem-X1-beta-at0314203142)
open import Examples.Groups.Clifford+CS.Five.D.D196 using (lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩-at3443 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at243243)
-- F4 CS12^0|CS01^1: 510 steps
lem-F4-CS12ᵖ0∣CS01ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (run b63)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx3-0412 ∷ Sb0-1-42-3 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b0 = at 3 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 3 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 2 3 (CCZ012 ∷ Bx3-4012 ∷ []) (lem-X1-beta-at0314203142 c4) ▸
       at 3 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 2 2 (Bx3-0412 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Bx3-0412 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at243243 c4) ▸ done

  b1 : Chain (X4 ∷ Bx3-0412 ∷ Sb0-1-42-3 ∷ CCZ012 ∷ X4 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Sb0-1-42-3 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b1 = at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 0 3 (CCZ012 ∷ Bx3-4012 ∷ []) (lem-X1-beta-at0314203142 c4) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 0 2 (Bx3-0412 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩ c4) ▸
       at 4 2 (X4 ∷ CCZ012 ∷ []) (lw3 c4 (CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CCZ012 ∷ []) (lw3 c4 (CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-42-3 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩-at3443 c4) ▸ done

  b2 : Chain (Bx3-0412 ∷ X4 ∷ Sb0-1-42-3 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b2 = at 3 2 (X4 ∷ CCZ012 ∷ []) (lw3 c4 (CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Bx3-0412 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b3 = at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS13⁻ ∷ []) (refl) ▸
       at 13 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b4 : Chain (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b4 = at 10 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS13 ∷ []) (refl) ▸
       at 7 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 2 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 2 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸ done

  b5 : Chain (Bx3-0412 ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b5 = at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 8 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 9 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b6 = at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b7 = at 23 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b8 : Chain (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b8 = at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 10 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (Bx3-0412 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b9 = at 9 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 4 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 2 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 3 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (Bx3-0412 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b10 = at 8 4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Bx3-0412 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b11 = at 11 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Bx3-0412 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b12 = at 2 4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 4 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b13 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b13 = at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸
       at 5 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 5 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b14 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b14 = at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (CS13⁻ ∷ []) (refl) ▸ done

  b15 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b15 = at 16 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 13 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS13 ∷ []) (refl) ▸
       at 10 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸ done

  b16 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b16 = at 5 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 5 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ Toff013 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b17 = at 10 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 13 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 14 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b18 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ Toff013 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b18 = at 15 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b19 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b19 = at 28 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b20 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b20 = at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b21 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b21 = at 16 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 17 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 17 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 19 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b22 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ X4 ∷ K2⁻ ∷ Toff013 ∷ X4 ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b22 = at 18 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 21 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 20 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 22 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 21 2 (CS12 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS12 ∷ []) (CS12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 23 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b23 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b23 = at 22 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 7 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 5 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 5 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b24 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b24 = at 7 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 8 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 9 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b25 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b25 = at 14 4 (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b26 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b26 = at 17 4 (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b27 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b27 = at 8 4 (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 10 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b28 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b28 = at 11 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 13 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 14 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b29 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b29 = at 13 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 16 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 15 2 (CS12 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS12 ∷ []) (CS12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 16 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b30 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b30 = at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸
       at 17 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 17 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b31 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ [])
  b31 = at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸ done

  b32 : Chain (Bx3-0412 ∷ Toff214 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K2 ∷ CCZ124 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b32 = at 5 1 (CS02 ∷ []) (refl) ▸
       at 4 2 (CS02 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 3 2 (Sb3-0-2-1 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at243243 c4) ▸
       at 3 1 (CS02 ∷ []) (refl) ▸
       at 2 2 (CS02 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 6 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸ done

  b33 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K2 ∷ CCZ124 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b33 = at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b34 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b34 = at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (CS13⁻ ∷ []) (refl) ▸
       at 15 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 12 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (CS13 ∷ []) (refl) ▸
       at 9 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b35 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b35 = at 13 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 6 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 4 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 4 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b36 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b36 = at 12 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 10 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b37 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b37 = at 14 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b38 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b38 = at 16 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b39 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b39 = at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 12 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 6 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b40 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b40 = at 4 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 5 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b41 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b41 = at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b42 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b42 = at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b43 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1342 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b43 = at 6 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 6 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸ done

  b44 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1342 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ [])
  b44 = at 7 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 7 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b45 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b45 = at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (CS13⁻ ∷ []) (refl) ▸
       at 18 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 15 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b46 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b46 = at 13 1 (CS13 ∷ []) (refl) ▸
       at 12 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 9 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 7 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 7 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b47 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b47 = at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b48 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ X4 ∷ Toff013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b48 = at 15 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 17 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 16 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 17 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b49 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b49 = at 22 4 (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b50 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b50 = at 25 4 (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 24 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 25 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b51 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b51 = at 16 4 (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 20 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b52 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b52 = at 19 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 19 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 21 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 23 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 22 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b53 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b53 = at 21 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 24 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 23 2 (CS12 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS12 ∷ []) (CS12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 25 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 24 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 9 15 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b54 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b54 = at 8 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 7 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 7 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 9 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 11 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b55 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ X4 ∷ Toff013 ∷ K2 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b55 = at 10 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b56 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b56 = at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CX13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b57 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b57 = at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b58 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b58 = at 12 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 12 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 14 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff013 ∷ X4 ∷ CX14 ∷ []) (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b59 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS12 ∷ Toff013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b59 = at 16 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 15 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 17 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 16 2 (K2 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2 ∷ []) (K2 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 18 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 17 2 (CS12 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS12 ∷ []) (CS12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b60 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS12 ∷ Toff013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Bx0-1342 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b60 = at 16 2 (CS12 ∷ X4 ∷ []) (sym (c₃ (CS ↑) (X ↑))) ▸
       at 19 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 (K2⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸ done

  b61 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Bx0-1342 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ [])
  b61 = at 19 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 19 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 5 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸ done

  b62 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ K2 ∷ CS24 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ [])
  b62 = at 6 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 6 2 (CS02⁻ ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸ done

  b63 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b63 = at 5 2 (Sb⁻3-0-2-1 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at243243 c4) ▸
       at 5 1 (CS02⁻ ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 0 1 (Sb2-0-41-3 ∷ []) (sym (lem-F0 c4)) ▸ done

