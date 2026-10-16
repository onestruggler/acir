{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D217 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at0114203243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym23-at12213443 ; lem-sym23-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at0110243243)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-X1-beta-at0114203243)
open import Examples.Groups.Clifford+CS.Five.D.D153 using (lem-sym34-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331)
open import Examples.Groups.Clifford+CS.Five.D.D157 using (lem-beta-T-at12213443 ; lem-sym34-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D216 using (lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩-at12233441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at122441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at122441 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at122441)
-- F4 CS23^0|CS02^1: 508 steps
lem-F4-CS23ᵖ0∣CS02ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣CS02ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (run b63)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (X4 ∷ Bx1-0423 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ CCZ023 ∷ X4 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b0 = at 3 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸
       at 2 3 (CCZ023 ∷ Bx1-4023 ∷ []) (lem-X1-beta-at0114203243 c4) ▸
       at 3 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸
       at 2 2 (Bx1-0423 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4) ▸
       at 1 2 (Bx1-0423 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at122441 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx1-0423 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ CCZ023 ∷ X4 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ023 ∷ CCZ023 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b1 = at 1 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸
       at 0 3 (CCZ023 ∷ Bx1-4023 ∷ []) (lem-X1-beta-at0114203243 c4) ▸
       at 1 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸
       at 0 2 (Bx1-0423 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4) ▸
       at 4 2 (X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-43-1 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩-at12233441 c4) ▸
       at 3 2 (X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx1-0423 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ023 ∷ CCZ023 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b2 = at 4 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b3 : Chain (Bx1-0423 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b3 = at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS12⁻ ∷ []) (refl) ▸
       at 13 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 10 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Bx1-0423 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b4 = at 8 1 (CS12 ∷ []) (refl) ▸
       at 7 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 2 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 2 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Bx1-0423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b5 = at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 8 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 7 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 9 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (Bx1-0423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b6 = at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Bx1-0423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b7 = at 20 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b8 : Chain (Bx1-0423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b8 = at 13 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 9 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b9 : Chain (Bx1-0423 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b9 = at 4 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 2 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 1 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (Bx1-0423 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b10 = at 6 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Bx1-0423 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b11 = at 8 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b12 = at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 4 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 3 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b13 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b13 = at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 5 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 5 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b14 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b14 = at 5 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (CS12⁻ ∷ []) (refl) ▸
       at 16 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2143 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b15 = at 29 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 13 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS12 ∷ []) (refl) ▸
       at 10 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 5 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸ done

  b16 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2143 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b16 = at 5 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 10 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b17 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b17 = at 11 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 12 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 14 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 13 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 15 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸ done

  b18 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b18 = at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b19 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b19 = at 29 4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b20 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b20 = at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 16 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸ done

  b21 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b21 = at 15 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 17 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 16 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 17 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 19 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 18 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b22 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b22 = at 21 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 20 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 19 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 22 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 21 2 (CS23 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CS23 ∷ []) (CS23 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 23 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 22 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸ done

  b23 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b23 = at 21 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 7 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 5 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 4 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 5 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 7 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸ done

  b24 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b24 = at 6 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 8 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 7 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 9 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b25 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b25 = at 12 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b26 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b26 = at 14 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b27 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b27 = at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 9 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸ done

  b28 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b28 = at 10 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 12 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 14 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 13 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b29 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b29 = at 16 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 15 2 (CS23 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CS23 ∷ []) (CS23 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 16 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 15 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b30 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b30 = at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 17 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 17 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b31 : Chain (Bx1-0423 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS03 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b31 = at 17 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸ done

  b32 : Chain (Bx1-0423 ∷ Toff324 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS03 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ K3 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ [])
  b32 = at 4 2 (CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb1-0-3-2 ∷ []) (refl) ▸
       at 3 2 (Sb1-0-3-2 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at122441 c4) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 2 2 (CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-3-2 ∷ []) (refl) ▸
       at 6 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸ done

  b33 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ K3 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ [])
  b33 = at 8 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b34 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ [])
  b34 = at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (CS12⁻ ∷ []) (refl) ▸
       at 15 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 12 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (CS12 ∷ []) (refl) ▸
       at 9 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b35 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ [])
  b35 = at 6 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 4 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 4 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b36 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ [])
  b36 = at 11 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸ done

  b37 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ [])
  b37 = at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b38 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ X4 ∷ K0 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ [])
  b38 = at 13 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b39 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ X4 ∷ K0 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ [])
  b39 = at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 12 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 6 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 4 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸ done

  b40 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ [])
  b40 = at 3 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 5 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b41 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ [])
  b41 = at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b42 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff012 ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ [])
  b42 = at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done

  b43 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff012 ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2413 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ [])
  b43 = at 7 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 6 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 5 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 7 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸ done

  b44 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2413 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ [])
  b44 = at 7 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b45 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b45 = at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (CS12⁻ ∷ []) (refl) ▸
       at 18 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 15 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS12 ∷ []) (refl) ▸ done

  b46 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b46 = at 12 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 9 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 7 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 7 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b47 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b47 = at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 13 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 15 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸ done

  b48 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ X4 ∷ K3⁻ ∷ Toff012 ∷ X4 ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b48 = at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 17 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 16 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 17 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b49 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b49 = at 20 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b50 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b50 = at 22 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 24 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 25 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b51 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b51 = at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 20 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 19 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸ done

  b52 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b52 = at 18 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 19 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 21 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 20 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 23 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 22 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 21 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b53 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ Toff012 ∷ X4 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ K3 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b53 = at 24 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 23 2 (CS23 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CS23 ∷ []) (CS23 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 25 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 24 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 23 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 9 15 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸ done

  b54 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ K3 ∷ X4 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b54 = at 7 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 6 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 7 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 9 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 8 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 11 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸ done

  b55 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ X4 ∷ K3 ∷ Toff012 ∷ X4 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b55 = at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0⁻ ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b56 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b56 = at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01⁻ ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX21 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CX21 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b57 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ X4 ∷ CS01 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b57 = at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ K0 ∷ X4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ X4 ∷ K0 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done

  b58 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ X4 ∷ Toff012 ∷ K3⁻ ∷ X4 ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b58 = at 13 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 12 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 14 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 13 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 12 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 13 4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ []) (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b59 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ X4 ∷ Toff012 ∷ K3⁻ ∷ X4 ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ X4 ∷ Toff012 ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b59 = at 15 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 14 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 17 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 16 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 15 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 18 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸
       at 17 2 (CS23 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CS23 ∷ []) (CS23 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (CS23 ∷ X4 ∷ []) (sym (c₄ (CS ↑ ↑) (X))) ▸ done

  b60 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ X4 ∷ Toff012 ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Bx0-2413 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b60 = at 19 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 18 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 17 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 19 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸ done

  b61 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Bx0-2413 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ [])
  b61 = at 19 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 5 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸ done

  b62 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ K3 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b62 = at 7 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 6 2 (CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 5 2 (Sb⁻1-0-3-2 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at122441 c4) ▸ done

  b63 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ X4 ∷ Sb⁻1-0-3-2 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (Sb1-0-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b63 = at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 2 (CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done

