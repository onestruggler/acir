{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D209 where

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
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F0-at132132 ; lem-beta-T-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D185 using (lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at122331)
open import Examples.Groups.Clifford+CS.Five.D.D189 using (lem-X1-beta-at02142041 ; lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at13213442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at2442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at2442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩-at2442 ; lem-sym12-at02102441 ; lem-sym12-at02142041)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-SBOX⟨1·0·43·2⟩)
-- F4 CS13^0|CS03^1: 422 steps
lem-F4-CS13ᵖ0∣CS03ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS13ᵖ0∣CS03ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (run b52))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (X4 ∷ Bx2-0431 ∷ Sb0-1-43-2 ∷ CCZ013 ∷ X4 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b0 = at 3 1 (Sb2-0-43-1 ∷ []) (lem-F0-at132132 c4) ▸
       at 3 1 (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx2-4031 ∷ []) (lem-sym12-at02102441 c4) ▸
       at 2 3 (CCZ013 ∷ Bx2-4031 ∷ []) (lem-X1-beta-at02142041 c4) ▸
       at 3 1 (Bx2-0431 ∷ []) (lem-sym12-at02142041 c4) ▸
       at 2 2 (Bx2-0431 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at132132 c4) ▸
       at 1 2 (Bx2-0431 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0231⟩-at2442 c4) ▸ done

  b1 : Chain (X4 ∷ Bx2-0431 ∷ Sb0-1-43-2 ∷ CCZ013 ∷ X4 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ X4 ∷ Sb0-1-43-2 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b1 = at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-4031 ∷ []) (lem-sym12-at02102441 c4) ▸
       at 0 3 (CCZ013 ∷ Bx2-4031 ∷ []) (lem-X1-beta-at02142041 c4) ▸
       at 1 1 (Bx2-0431 ∷ []) (lem-sym12-at02142041 c4) ▸
       at 0 2 (Bx2-0431 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at132132 c4) ▸
       at 4 2 (X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-43-2 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·2·31·4⟩-at13213442 c4) ▸ done

  b2 : Chain (Bx2-0431 ∷ X4 ∷ Sb0-1-43-2 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b2 = at 3 2 (X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Bx2-0431 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b3 = at 2 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS12 ∷ []) (refl) ▸
       at 14 1 (CS12⁻ ∷ []) (refl) ▸
       at 7 12 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Bx2-0431 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b4 = at 11 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 17 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 4 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b5 : Chain (Bx2-0431 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b5 = at 11 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 12 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (Bx2-0431 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b6 = at 20 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b7 : Chain (Bx2-0431 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b7 = at 13 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 13 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 7 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 5 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b8 : Chain (Bx2-0431 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b8 = at 6 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (Bx2-0431 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b9 = at 8 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b10 : Chain (Bx2-0431 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b10 = at 7 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 1 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b11 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b11 = at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 5 (Sb0-1-43-2 ∷ []) (refl) ▸
       at 5 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b12 = at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS12 ∷ []) (refl) ▸
       at 17 1 (CS12⁻ ∷ []) (refl) ▸
       at 10 21 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 29 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 7 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸ done

  b13 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b13 = at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b14 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b14 = at 16 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 17 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 18 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS02 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b15 = at 25 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 29 4 (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 26 4 (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS14⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 4 (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS02 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b16 = at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 19 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b17 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b17 = at 20 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 20 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 22 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 24 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 23 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b18 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b18 = at 22 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 25 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 24 2 (CS13 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 26 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 25 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 10 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b19 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b19 = at 9 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 8 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 8 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 10 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b20 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b20 = at 11 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 12 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 23 4 (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b21 = at 20 4 (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 4 (CS14⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 4 (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b22 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b22 = at 13 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 13 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b23 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS13 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b23 = at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 16 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 17 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 18 2 (CS13 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b24 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS13 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b24 = at 17 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 19 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 4 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b25 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ K1 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b25 = at 17 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 5 (Sb0-1-43-2 ∷ []) (refl) ▸
       at 3 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸ done

  b26 : Chain (Bx2-0431 ∷ K1 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ X4 ∷ Sb2-0-1-3 ∷ Sb0-1-43-2 ∷ X4 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ [])
  b26 = at 5 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS01 ∷ []) (refl) ▸
       at 4 2 (CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ []) (CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb2-0-1-3 ∷ []) (refl) ▸
       at 3 2 (Sb2-0-1-3 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·1·3⟩-at2442 c4) ▸ done

  b27 : Chain (Bx2-0431 ∷ Toff134 ∷ X4 ∷ Sb2-0-1-3 ∷ Sb0-1-43-2 ∷ X4 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ [])
  b27 = at 3 1 (CS01 ∷ []) (refl) ▸
       at 2 2 (CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ []) (CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-1-3 ∷ []) (refl) ▸
       at 6 1 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸ done

  b28 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ [])
  b28 = at 17 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (CS12 ∷ []) (refl) ▸
       at 16 1 (CS12⁻ ∷ []) (refl) ▸ done

  b29 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ [])
  b29 = at 9 12 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 19 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 6 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b30 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ [])
  b30 = at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b31 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ [])
  b31 = at 25 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b32 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ [])
  b32 = at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 15 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 9 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 7 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b33 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ [])
  b33 = at 6 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 8 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b34 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ [])
  b34 = at 13 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b35 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ [])
  b35 = at 10 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 9 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 3 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸ done

  b36 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ [])
  b36 = at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (Sb0-1-43-2 ∷ []) (refl) ▸
       at 7 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b37 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ [])
  b37 = at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS12 ∷ []) (refl) ▸
       at 19 1 (CS12⁻ ∷ []) (refl) ▸
       at 12 21 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 31 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 9 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b38 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx0-1432 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ [])
  b38 = at 7 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b39 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ [])
  b39 = at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 20 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 20 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b40 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ [])
  b40 = at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 31 4 (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 28 4 (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 4 (CS14⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b41 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ [])
  b41 = at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 24 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 25 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b42 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ [])
  b42 = at 23 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 22 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 22 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 24 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 26 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b43 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ K1 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ [])
  b43 = at 25 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 27 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 26 2 (CS13 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 28 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 27 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 26 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b44 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ [])
  b44 = at 12 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 10 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 10 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 12 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b45 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ [])
  b45 = at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b46 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ X4 ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ [])
  b46 = at 25 4 (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS14⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX32 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CX32 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b47 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ [])
  b47 = at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 16 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 15 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b48 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CCZ023 ∷ CS13 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ [])
  b48 = at 16 4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 20 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 21 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸ done

  b49 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ CCZ023 ∷ CS13 ∷ X4 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ [])
  b49 = at 20 2 (CS13 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 22 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 2 (K1⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 6 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b50 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb0-1-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻0-1-2-3 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ [])
  b50 = at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸
       at 20 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 21 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 22 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 23 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 19 5 (Sb0-1-43-2 ∷ []) (refl) ▸
       at 5 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸ done

  b51 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ K1 ∷ CS14 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ Sb⁻2-0-1-3 ∷ []) (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ X4 ∷ Sb0-1-43-2 ∷ Sb⁻2-0-1-3 ∷ X4 ∷ [])
  b51 = at 6 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS01⁻ ∷ []) (refl) ▸
       at 6 2 (CS01⁻ ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻2-0-1-3 ∷ []) (refl) ▸ done

  b52 : Chain (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ X4 ∷ Sb0-1-43-2 ∷ Sb⁻2-0-1-3 ∷ X4 ∷ []) (Sb1-0-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ [])
  b52 = at 5 2 (Sb⁻2-0-1-3 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·1·3⟩-at2442 c4) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 4 2 (CS01⁻ ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻2-0-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-43-1 ∷ []) (refl) ▸
       at 0 1 (Sb1-0-43-2 ∷ []) (sym (lem-F0-at132132 c4)) ▸ done


-- auto CCZ012 | SBOX(3;0;42;1) @01122330: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at01122330 : Complete 4 → ⟪ (CCZ123 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at01122330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at122331 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done

