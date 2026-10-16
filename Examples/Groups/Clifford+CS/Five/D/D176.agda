{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D176 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0189 ; wl0190 ; wl0211 ; wl0260 ; wl0283 ; wl0433 ; wl0548 ; wl0560 ; wl0724 ; wl0725 ; wl0726 ; wl0727 ; wl0728 ; wl0733 ; wl0734 ; wl0743 ; wl0744 ; wl0745 ; wl0746 ; wp0296 ; wp0343 ; wp0344 ; wp0345 ; wp0346 ; wp0365 ; wp0366 ; wp0373 ; wp0374 ; wp0375 ; wp0376 ; wp0377 ; wp0378 ; wp0379 ; wp0380 ; wp0381 ; wp0382 ; wp0383 ; wp0384 ; wp0387 ; wp0388)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-beta-T-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-beta-T-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D175 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0210243143)
-- F4 CS01^0|CS23^1 part0: 500 steps
lem-F4-CS01ᵖ0∣CS23ᵖ1-part0 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣CS23ᵖ1-part0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 3 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0373 c4)) ▸
       at 4 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp0374 c4) ▸
       at 5 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 8 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 11 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 14 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 13 1 (CS03⁻ ∷ []) (refl) ▸
       at 6 12 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0375 c4)) ▸ done

  b2 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b2 = at 10 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 16 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wp0376 c4)) ▸
       at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b3 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b3 = at 10 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 9 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 11 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸ done

  b4 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b4 = at 19 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 16 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 13 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 10 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸ done

  b5 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b5 = at 12 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 13 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 12 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 11 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 6 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0377 c4)) ▸
       at 5 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 4 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 3 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b6 : Chain (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b6 = at 5 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 13 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 10 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸ done

  b7 : Chain (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b7 = at 7 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 4 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 7 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸ done

  b8 : Chain (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b8 = at 6 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 5 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 0 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0377 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b9 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b9 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 4 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 4 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b10 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b10 = at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 1 (CS02 ∷ []) (refl) ▸
       at 16 1 (CS02⁻ ∷ []) (refl) ▸
       at 9 21 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (sym (wp0378 c4)) ▸
       at 22 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 28 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 6 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (sym (wp0379 c4)) ▸ done

  b11 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b11 = at 4 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 13 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 12 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 13 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸ done

  b12 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b12 = at 16 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 15 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 14 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 17 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 16 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 15 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 17 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0211 (lit c4)) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b13 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b13 = at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 28 4 (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wp0380 c4)) ▸
       at 25 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 22 4 (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0382 c4)) ▸
       at 19 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 16 4 (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0383 c4)) ▸ done

  b14 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b14 = at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 18 5 (CCZ123 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 19 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 18 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 17 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸ done

  b15 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b15 = at 20 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 19 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 18 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 19 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸
       at 22 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 21 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 20 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 23 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b16 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b16 = at 22 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 21 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 24 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 23 2 (CS02 ∷ CCZ123 ∷ []) (wl0734 (lit c4)) ▸
       at 22 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 25 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 24 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 23 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸ done

  b17 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b17 = at 9 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (sym (wp0384 c4)) ▸
       at 8 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 7 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 6 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 7 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸
       at 10 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 9 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 8 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸ done

  b18 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b18 = at 11 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 10 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 9 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 11 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0211 (lit c4)) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b19 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b19 = at 22 4 (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wp0380 c4)) ▸
       at 19 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 16 4 (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0382 c4)) ▸
       at 13 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 10 4 (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0383 c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸ done

  b20 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b20 = at 16 2 [] (wl0283 (lit c4)) ▸
       at 12 5 (CCZ123 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 13 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 12 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 11 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 14 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 13 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 12 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b21 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CCZ123 ∷ CS02 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b21 = at 13 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸
       at 16 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 15 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 14 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 17 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 16 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 15 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 18 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸ done

  b22 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CCZ123 ∷ CS02 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b22 = at 17 2 (CS02 ∷ CCZ123 ∷ []) (wl0734 (lit c4)) ▸
       at 16 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 19 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 18 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 17 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 3 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (sym (wp0384 c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸ done

  b23 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b23 = at 19 2 [] (wl0283 (lit c4)) ▸
       at 16 4 (Bx3-0412 ∷ []) (sym (lem-beta-T-at0310243142 c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 16 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 16 1 (Sb2-0-41-3 ∷ []) (sym (lem-F0 c4)) ▸ done

  b24 : Chain (K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ X4 ∷ CCZ013 ∷ Sb2-0-41-3 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b24 = at 2 2 [] (wl0189 (lit c4)) ▸
       at 3 2 [] (wl0189 (lit c4)) ▸
       at 4 2 [] (wl0189 (lit c4)) ▸
       at 5 2 [] (wl0189 (lit c4)) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0374 c4)) ▸
       at 0 3 (Toff024 ∷ []) (wp0373 c4) ▸
       at 3 2 (CCZ013 ∷ X4 ∷ []) (sym (wp0296 c4)) ▸
       at 2 2 (CCZ013 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0210243143 c4) ▸ done

  b25 : Chain (Toff024 ∷ X4 ∷ CCZ013 ∷ Sb2-0-41-3 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b25 = at 1 2 (CCZ013 ∷ X4 ∷ []) (sym (wp0296 c4)) ▸
       at 5 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0373 c4)) ▸
       at 6 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp0374 c4) ▸
       at 7 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 10 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 13 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 16 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b26 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b26 = at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 1 (CS03 ∷ []) (refl) ▸
       at 15 1 (CS03⁻ ∷ []) (refl) ▸
       at 8 12 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0375 c4)) ▸
       at 12 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b27 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b27 = at 18 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wp0376 c4)) ▸
       at 3 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 12 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸ done

  b28 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b28 = at 11 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 13 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 21 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸ done

  b29 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b29 = at 18 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 15 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 12 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 14 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸ done

  b30 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b30 = at 15 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 14 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 13 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 8 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0377 c4)) ▸
       at 7 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 6 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 5 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 7 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸ done

  b31 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X4 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b31 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 15 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 12 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 9 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸ done

  b32 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ K0⁻ ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b32 = at 6 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 8 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 9 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 8 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸ done

  b33 : Chain (Toff024 ∷ CCZ013 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ K0⁻ ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b33 = at 7 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 2 6 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0377 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸ done

  b34 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b34 = at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 6 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 6 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b35 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Bx3-0412 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b35 = at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 1 (CS02 ∷ []) (refl) ▸
       at 18 1 (CS02⁻ ∷ []) (refl) ▸
       at 11 21 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (sym (wp0378 c4)) ▸
       at 24 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 30 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 8 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (sym (wp0379 c4)) ▸
       at 6 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4) ▸ done

  b36 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b36 = at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 15 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 14 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 15 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸
       at 18 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸ done

  b37 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ X4 ∷ CCZ123 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b37 = at 17 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 16 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 19 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 18 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 17 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 19 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0211 (lit c4)) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b38 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b38 = at 26 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 29 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 30 4 (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wp0380 c4)) ▸
       at 27 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 24 4 (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0382 c4)) ▸
       at 21 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 18 4 (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0383 c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸ done

  b39 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b39 = at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 24 2 [] (wl0283 (lit c4)) ▸
       at 20 5 (CCZ123 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 21 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 20 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 19 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 22 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b40 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b40 = at 21 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 20 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 21 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸
       at 24 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 23 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 22 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 25 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 24 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸ done

  b41 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ K0 ∷ CCZ123 ∷ X4 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b41 = at 23 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 26 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 25 2 (CS02 ∷ CCZ123 ∷ []) (wl0734 (lit c4)) ▸
       at 24 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 27 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 26 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 25 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 11 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (sym (wp0384 c4)) ▸ done

  b42 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b42 = at 10 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 9 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 8 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 9 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸
       at 12 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 11 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 10 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 13 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b43 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ X4 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b43 = at 12 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 11 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 13 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0211 (lit c4)) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 4 (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wp0380 c4)) ▸ done

  b44 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b44 = at 21 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 18 4 (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0382 c4)) ▸
       at 15 4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (sym (wp0381 c4)) ▸
       at 12 4 (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0383 c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸ done

  b45 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b45 = at 14 5 (CCZ123 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 15 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 14 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 13 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 16 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 15 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 14 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 15 4 (CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0733 (lit c4))) ▸ done

  b46 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS02 ∷ CCZ123 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b46 = at 18 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 17 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 16 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 19 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 18 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 17 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 20 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 19 2 (CS02 ∷ CCZ123 ∷ []) (wl0734 (lit c4)) ▸ done

  b47 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ X4 ∷ CS02 ∷ CCZ123 ∷ X4 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b47 = at 18 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 21 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 20 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (c₁ (K • iI) (CCZ))) ▸
       at 19 2 (K0⁻ ∷ X4 ∷ []) (sym (c₁ (K • iI) (X ↑ ↑ ↑))) ▸
       at 5 15 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (sym (wp0384 c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸ done

  b48 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb3-0-2-1 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ Sb⁻3-0-2-1 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b48 = at 18 4 (Bx3-0412 ∷ []) (sym (lem-beta-T-at0310243142 c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 18 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 18 1 (Sb2-0-41-3 ∷ []) (sym (lem-F0 c4)) ▸
       at 4 2 [] (wl0189 (lit c4)) ▸ done

  b49 : Chain (Toff024 ∷ CCZ013 ∷ K0 ∷ CS04 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b49 = at 5 2 [] (wl0189 (lit c4)) ▸
       at 6 2 [] (wl0189 (lit c4)) ▸
       at 7 2 [] (wl0189 (lit c4)) ▸
       at 3 5 (CCZ024 ∷ []) (sym (wp0374 c4)) ▸
       at 2 3 (Toff024 ∷ []) (wp0373 c4) ▸
       at 5 2 (CCZ013 ∷ X4 ∷ []) (sym (wp0296 c4)) ▸
       at 4 2 (CCZ013 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0210243143 c4) ▸
       at 3 2 (CCZ013 ∷ X4 ∷ []) (sym (wp0296 c4)) ▸ done

  b50 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b50 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 4 1 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (sym (wl0743 (lit c4))) ▸
       at 5 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4)) ▸
       at 6 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 9 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 12 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 15 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b51 : Chain (Bx0-2431 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b51 = at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS03⁻ ∷ []) (refl) ▸
       at 13 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0387 c4)) ▸
       at 17 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 10 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0744 (lit c4))) ▸ done

  b52 : Chain (Bx0-2431 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b52 = at 8 1 (CS03 ∷ []) (refl) ▸
       at 7 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0388 c4)) ▸
       at 11 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0744 (lit c4))) ▸
       at 2 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 2 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 2 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b53 : Chain (Bx0-2431 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b53 = at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0745 (lit c4))) ▸
       at 9 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 8 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 7 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 9 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b54 : Chain (Bx0-2431 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b54 = at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 4 (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 12 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸ done

  b55 : Chain (Bx0-2431 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b55 = at 20 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 17 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0726 (lit c4))) ▸
       at 14 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 11 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸ done

  b56 : Chain (Bx0-2431 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b56 = at 13 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 8 4 (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0728 (lit c4))) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 10 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 11 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 10 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 9 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸ done

  b57 : Chain (Bx0-2431 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b57 = at 4 6 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0745 (lit c4))) ▸
       at 3 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 2 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 1 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 3 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 4 (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸ done

  b58 : Chain (Bx0-2431 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b58 = at 6 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 14 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 11 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0726 (lit c4))) ▸ done

  b59 : Chain (Bx0-2431 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b59 = at 8 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 5 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 2 4 (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0728 (lit c4))) ▸ done

  b60 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1⁻ ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b60 = at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 4 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 5 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 4 2 (K1⁻ ∷ Toff203 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 3 2 (K1⁻ ∷ X4 ∷ []) (sym (c₂ ((K • iI) ↑) (X ↑ ↑))) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸ done

  b61 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b61 = at 8 2 [] (wl0283 (lit c4)) ▸
       at 5 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 5 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 5 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸ done

  b62 : Chain (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b62 = at 5 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

