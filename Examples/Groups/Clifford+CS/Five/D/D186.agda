{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D186 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0190 ; wl0247 ; wl0248 ; wl0249 ; wl0250 ; wl0260 ; wl0283 ; wl0548 ; wl0560 ; wl0724 ; wl0725 ; wl0726 ; wl0727 ; wl0728 ; wl0743 ; wl0744 ; wl0745 ; wl0746 ; wl0747 ; wl0748 ; wl0749 ; wl0750 ; wl0751 ; wl0752 ; wl0753 ; wl0754 ; wl0755 ; wl0885 ; wl0886 ; wl0887 ; wl0888 ; wp0034 ; wp0059 ; wp0365 ; wp0366 ; wp0387 ; wp0388 ; wp0389 ; wp0390 ; wp0391 ; wp0392 ; wp0393 ; wp0461 ; wp0462 ; wp0463 ; wp0464 ; wp0465)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F5-CS01)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-F4-iIᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-F4-CS01ᵖ0∣iIᵖ1 ; lem-F4-K1ᵖ0∣CS01ᵖ1 ; lem-F4-S0ᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-F4-CS01ᵖ0∣CS01ᵖ1 ; lem-F4-CS01ᵖ0∣K1ᵖ1 ; lem-F4-CS01ᵖ0∣S0ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D184 using (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D185 using (lem-F2-CS01∣CS23-part0)
-- F2 CS01|CS23 part1: 475 steps
lem-F2-CS01∣CS23-part1 : Ws → ⟪ (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F2-CS01∣CS23-part1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (run b59)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b0 = at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 28 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 29 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 26 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 23 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0726 (lit c4))) ▸
       at 20 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸ done

  b1 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K2 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b1 = at 17 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 19 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 14 4 (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0728 (lit c4))) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸ done

  b2 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K2 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b2 = at 18 2 [] (wl0283 (lit c4)) ▸
       at 16 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 16 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 15 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸ done

  b3 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b3 = at 17 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 17 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 17 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 17 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 10 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0744 (lit c4))) ▸
       at 8 1 (CS03⁻ ∷ []) (refl) ▸
       at 7 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0387 c4)) ▸
       at 11 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b4 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b4 = at 4 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0744 (lit c4))) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 1 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0388 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸ done

  b5 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx2-0431 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b5 = at 5 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 5 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 17 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸ done

  b6 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx2-0431 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b6 = at 17 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 17 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0748 (lit c4))) ▸
       at 24 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 23 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸ done

  b7 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b7 = at 22 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 23 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 26 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 25 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 24 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 27 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 26 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 25 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b8 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b8 = at 27 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 28 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 31 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 32 4 (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0749 (lit c4))) ▸
       at 30 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 31 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 34 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 37 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b9 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b9 = at 40 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 41 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0392 c4)) ▸
       at 38 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸
       at 35 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0750 (lit c4))) ▸
       at 32 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸
       at 29 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0751 (lit c4))) ▸
       at 32 2 [] (wl0283 (lit c4)) ▸
       at 33 2 [] (wl0283 (lit c4)) ▸ done

  b10 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b10 = at 34 2 [] (wl0283 (lit c4)) ▸
       at 35 2 [] (wl0283 (lit c4)) ▸
       at 31 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 26 4 (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0752 (lit c4))) ▸
       at 29 2 [] (wl0283 (lit c4)) ▸
       at 30 2 [] (wl0283 (lit c4)) ▸
       at 28 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 29 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b11 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ K1⁻ ∷ Toff203 ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b11 = at 28 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 27 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 30 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 29 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 28 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 29 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 32 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 31 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸ done

  b12 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ K1⁻ ∷ Toff203 ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b12 = at 30 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 33 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 32 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 31 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 34 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 33 2 (CS13 ∷ Toff203 ∷ []) (sym (wl0753 (lit c4))) ▸
       at 32 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 35 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b13 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b13 = at 34 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 33 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 19 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0748 (lit c4))) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 17 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 16 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 17 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b14 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b14 = at 19 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 18 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 20 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 19 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 21 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b15 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b15 = at 26 4 (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0749 (lit c4))) ▸
       at 24 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 25 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 28 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 31 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 34 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 35 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0392 c4)) ▸
       at 32 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸ done

  b16 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b16 = at 29 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0750 (lit c4))) ▸
       at 26 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸
       at 23 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0751 (lit c4))) ▸
       at 26 2 [] (wl0283 (lit c4)) ▸
       at 27 2 [] (wl0283 (lit c4)) ▸
       at 28 2 [] (wl0283 (lit c4)) ▸
       at 29 2 [] (wl0283 (lit c4)) ▸
       at 25 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸ done

  b17 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b17 = at 20 4 (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0752 (lit c4))) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 24 2 [] (wl0283 (lit c4)) ▸
       at 22 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 22 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 21 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 24 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b18 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b18 = at 23 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 22 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 23 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 26 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 25 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 24 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 27 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 26 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸ done

  b19 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b19 = at 25 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 28 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 27 2 (CS13 ∷ Toff203 ∷ []) (sym (wl0753 (lit c4))) ▸
       at 26 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 29 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 28 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 27 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 30 2 [] (wl0283 (lit c4)) ▸ done

  b20 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b20 = at 31 2 [] (wl0283 (lit c4)) ▸
       at 32 2 [] (wl0283 (lit c4)) ▸
       at 29 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 29 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 29 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 29 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 13 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0747 (lit c4))) ▸
       at 11 1 (CS03⁻ ∷ []) (refl) ▸ done

  b21 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b21 = at 10 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0389 c4)) ▸
       at 23 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 7 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0747 (lit c4))) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 4 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0390 c4)) ▸
       at 17 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸ done

  b22 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ K1 ∷ CCZ134 ∷ K1⁻ ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b22 = at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 17 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 3 2 [] (wl0260 (lit c4)) ▸
       at 4 2 [] (wl0260 (lit c4)) ▸
       at 5 2 [] (wl0260 (lit c4)) ▸
       at 6 2 [] (wl0260 (lit c4)) ▸
       at 2 5 (CCZ134 ∷ []) (sym (wl0190 (lit c4))) ▸ done

  b23 : Chain (Bx0-2431 ∷ K1 ∷ CCZ134 ∷ K1⁻ ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b23 = at 1 3 (Toff134 ∷ []) (wl0743 (lit c4)) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 4 2 (CS12 ∷ X4 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 4 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 2 (Sb0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 c4) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ X4 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b24 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b24 = at 6 1 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (sym (wl0743 (lit c4))) ▸
       at 7 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4)) ▸
       at 8 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 11 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 14 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 17 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 4 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b25 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b25 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 16 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 16 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 16 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b26 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b26 = at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0745 (lit c4))) ▸
       at 23 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 22 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 23 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b27 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b27 = at 27 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 28 4 (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 26 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 33 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 36 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 37 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸ done

  b28 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b28 = at 34 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 31 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0726 (lit c4))) ▸
       at 28 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 25 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 28 2 [] (wl0283 (lit c4)) ▸
       at 29 2 [] (wl0283 (lit c4)) ▸
       at 30 2 [] (wl0283 (lit c4)) ▸
       at 31 2 [] (wl0283 (lit c4)) ▸ done

  b29 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b29 = at 27 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 22 4 (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0728 (lit c4))) ▸
       at 25 2 [] (wl0283 (lit c4)) ▸
       at 26 2 [] (wl0283 (lit c4)) ▸
       at 24 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 25 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 24 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b30 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b30 = at 18 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0745 (lit c4))) ▸
       at 17 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 16 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 15 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 17 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 4 (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸ done

  b31 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b31 = at 20 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 31 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 28 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 25 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0726 (lit c4))) ▸ done

  b32 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b32 = at 22 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 19 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 24 2 [] (wl0283 (lit c4)) ▸
       at 25 2 [] (wl0283 (lit c4)) ▸
       at 21 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 16 4 (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0728 (lit c4))) ▸ done

  b33 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b33 = at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 18 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 19 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 18 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 17 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸ done

  b34 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b34 = at 22 2 [] (wl0283 (lit c4)) ▸
       at 19 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 19 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 19 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 19 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 12 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0744 (lit c4))) ▸
       at 10 1 (CS03⁻ ∷ []) (refl) ▸
       at 9 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0387 c4)) ▸ done

  b35 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b35 = at 13 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0744 (lit c4))) ▸
       at 4 1 (CS03 ∷ []) (refl) ▸
       at 3 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0388 c4)) ▸
       at 7 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b36 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b36 = at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 7 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸ done

  b37 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b37 = at 19 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 19 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 19 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 26 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 27 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0748 (lit c4))) ▸
       at 26 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b38 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b38 = at 25 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 24 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 25 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 28 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 27 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 26 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 29 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 28 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸ done

  b39 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ K1 ∷ Toff203 ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b39 = at 27 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 29 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 33 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 34 4 (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0749 (lit c4))) ▸
       at 32 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 33 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 36 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b40 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b40 = at 39 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 42 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 43 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0392 c4)) ▸
       at 40 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸
       at 37 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0750 (lit c4))) ▸
       at 34 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸
       at 31 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0751 (lit c4))) ▸
       at 34 2 [] (wl0283 (lit c4)) ▸ done

  b41 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b41 = at 35 2 [] (wl0283 (lit c4)) ▸
       at 36 2 [] (wl0283 (lit c4)) ▸
       at 37 2 [] (wl0283 (lit c4)) ▸
       at 33 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 28 4 (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0752 (lit c4))) ▸
       at 31 2 [] (wl0283 (lit c4)) ▸
       at 32 2 [] (wl0283 (lit c4)) ▸
       at 30 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸ done

  b42 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b42 = at 31 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 30 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 29 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 32 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 31 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 30 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 31 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 34 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b43 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ X4 ∷ Toff203 ∷ K1⁻ ∷ X4 ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b43 = at 33 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 32 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 35 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 34 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 33 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 36 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 35 2 (CS13 ∷ Toff203 ∷ []) (sym (wl0753 (lit c4))) ▸
       at 34 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸ done

  b44 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ X4 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b44 = at 37 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 36 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 35 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0748 (lit c4))) ▸
       at 20 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 18 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 19 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸ done

  b45 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b45 = at 22 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 21 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 20 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 23 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 22 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 21 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 23 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b46 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b46 = at 27 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 28 4 (CS14⁻ ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0749 (lit c4))) ▸
       at 26 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 30 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 33 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 36 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 37 4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0392 c4)) ▸ done

  b47 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b47 = at 34 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸
       at 31 4 (CS14⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0750 (lit c4))) ▸
       at 28 4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0393 c4)) ▸
       at 25 4 (CS14⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0751 (lit c4))) ▸
       at 28 2 [] (wl0283 (lit c4)) ▸
       at 29 2 [] (wl0283 (lit c4)) ▸
       at 30 2 [] (wl0283 (lit c4)) ▸
       at 31 2 [] (wl0283 (lit c4)) ▸ done

  b48 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14⁻ ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b48 = at 27 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 22 4 (CS14⁻ ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0752 (lit c4))) ▸
       at 25 2 [] (wl0283 (lit c4)) ▸
       at 26 2 [] (wl0283 (lit c4)) ▸
       at 24 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 25 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 24 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 23 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b49 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b49 = at 26 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 25 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 24 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 25 4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (sym (wp0391 c4)) ▸
       at 28 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 27 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 26 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 29 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b50 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b50 = at 28 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 27 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 30 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 29 2 (CS13 ∷ Toff203 ∷ []) (sym (wl0753 (lit c4))) ▸
       at 28 2 (CS13 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))) ▸
       at 31 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 30 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 29 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b51 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b51 = at 32 2 [] (wl0283 (lit c4)) ▸
       at 33 2 [] (wl0283 (lit c4)) ▸
       at 34 2 [] (wl0283 (lit c4)) ▸
       at 31 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 31 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 31 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 31 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 15 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0747 (lit c4))) ▸ done

  b52 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b52 = at 13 1 (CS03⁻ ∷ []) (refl) ▸
       at 12 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0389 c4)) ▸
       at 25 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 9 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0747 (lit c4))) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 6 15 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0390 c4)) ▸
       at 19 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸ done

  b53 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Bx⁻2-0413 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ [])
  b53 = at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 19 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 5 2 [] (wl0260 (lit c4)) ▸
       at 6 2 [] (wl0260 (lit c4)) ▸
       at 7 2 [] (wl0260 (lit c4)) ▸
       at 8 2 [] (wl0260 (lit c4)) ▸ done

  b54 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ CS01 ∷ [])
  b54 = at 4 5 (CCZ134 ∷ []) (sym (wl0190 (lit c4))) ▸
       at 3 3 (Toff134 ∷ []) (wl0743 (lit c4)) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 2 (CS12⁻ ∷ X4 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 6 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 2 (Sb⁻0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 c4) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ X4 ∷ []) (sym (wl0755 (lit c4))) ▸ done

  b55 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ CS01 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b55 = at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 4 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 7 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 6 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸ done

  b56 : Chain (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b56 = at 11 2 [] (wp0034 c4) ▸
       at 10 2 [] (wp0059 c4) ▸
       at 9 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 9 1 (CZ03 ∷ []) (refl) ▸
       at 12 1 (CZ03 ∷ []) (refl) ▸
       at 15 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 17 1 (CZ03 ∷ []) (refl) ▸
       at 20 1 (CZ03 ∷ []) (refl) ▸ done

  b57 : Chain (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b57 = at 9 12 [] (wl0247 (lit c4)) ▸
       at 8 2 [] (wp0059 c4) ▸
       at 7 2 [] (wp0034 c4) ▸
       at 6 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 6 1 (CZ03 ∷ []) (refl) ▸
       at 9 1 (CZ03 ∷ []) (refl) ▸
       at 12 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 14 1 (CZ03 ∷ []) (refl) ▸ done

  b58 : Chain (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS03 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b58 = at 17 1 (CZ03 ∷ []) (refl) ▸
       at 6 12 [] (wl0247 (lit c4)) ▸
       at 5 2 [] (wl0248 (lit c4)) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 4 2 [] (wl0249 (lit c4)) ▸
       at 3 2 [] (wl0248 (lit c4)) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸ done

  b59 : Chain (Sb0-2-43-1 ∷ X4 ∷ CS03 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ [])
  b59 = at 3 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 2 [] (wl0250 (lit c4)) ▸
       at 1 2 [] (wl0283 (lit c4)) ▸ done


-- F2 CS01|CS23: 2 steps
lem-F2-CS01∣CS23 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F2-CS01∣CS23 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 2 (Bx0-2431 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS01 ∷ []) (lem-F2-CS01∣CS23-part0 c4) ▸
       at 0 54 (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) (lem-F2-CS01∣CS23-part1 c4) ▸ done


-- split4[CS01 CS01 CS01 CS01 CS01 CS01 S0 iI S0 S0 S0 CS01 K1 CS01 K1 CS01]: 136 steps
lem-split4CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 : Ws → ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-split4CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 15 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 14 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸
       at 13 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 12 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸
       at 11 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 10 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4) ▸
       at 9 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4) ▸
       at 8 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4) ▸ done

  b1 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b1 = at 7 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl0886 (lit c4))) ▸
       at 6 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4) ▸
       at 5 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 4 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 3 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 2 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 1 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 0 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b2 = at 3 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 7 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 6 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 11 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 10 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 9 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 14 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b3 = at 13 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 12 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 19 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 18 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 17 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 16 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 23 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b4 = at 22 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 21 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 20 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 19 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 18 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (wp0462 c4) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS01ᵖ1 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS01ᵖ1 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b5 = at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS01ᵖ1 c4)) ▸
       at 23 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS01ᵖ1 c4)) ▸
       at 22 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS01ᵖ1 c4)) ▸
       at 21 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS01ᵖ1 c4)) ▸
       at 31 4 (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4) ▸
       at 30 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 29 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 28 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b6 = at 27 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 26 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 25 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 24 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 35 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 34 4 (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4) ▸
       at 33 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 32 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b7 = at 31 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 30 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 29 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 28 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 27 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 39 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 38 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 37 4 (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4) ▸ done

  b8 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b8 = at 36 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 35 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 34 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 33 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 32 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 31 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 30 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 43 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸ done

  b9 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b9 = at 42 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 41 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 40 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS01ᵖ0∣iIᵖ1 c4)) ▸
       at 39 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 38 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 37 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 36 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 35 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸ done

  b10 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b10 = at 34 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 33 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 47 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 46 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 45 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 44 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 43 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸
       at 42 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸ done

  b11 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b11 = at 41 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 40 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 39 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 38 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 37 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 36 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 51 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 50 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸ done

  b12 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b12 = at 49 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 48 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 47 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 46 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS01ᵖ0∣iIᵖ1 c4)) ▸
       at 45 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 44 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 43 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 42 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸ done

  b13 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b13 = at 41 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 40 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 39 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 55 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 54 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4)) ▸
       at 53 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 52 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 51 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸ done

  b14 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b14 = at 50 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 49 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸
       at 48 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 47 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 46 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 45 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 44 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 43 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸ done

  b15 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b15 = at 42 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 59 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 58 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 57 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 56 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 55 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 54 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 53 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸ done

  b16 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b16 = at 52 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS01ᵖ0∣iIᵖ1 c4)) ▸
       at 51 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 50 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 49 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 48 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 47 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 46 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 45 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸ done

