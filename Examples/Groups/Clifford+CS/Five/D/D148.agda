{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D148 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0509 ; wl0514 ; wl0528 ; wl0529 ; wl0530 ; wl0531 ; wl0548 ; wl0550 ; wl0551 ; wl0554 ; wl0558 ; wl0571 ; wl0572 ; wl0579 ; wl0580 ; wl0581 ; wl0582 ; wl0583 ; wl0584 ; wl0585 ; wp0200 ; wp0201 ; wp0202 ; wp0203 ; wp0204 ; wp0225 ; wp0245 ; wp0246 ; wp0247 ; wp0248)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-beta-T-at0310243142 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-auto-CCZ012-∣-CCZ314-at0112243043 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0210243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 ; lem-beta-T-at03103441 ; lem-sym23-at0310243241 ; lem-sym23-at03103441 ; lem-sym34-at0310243142 ; lem-sym34-at0310243241)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CCZ134-CX20)
-- F1 CS-K1 part24: 341 steps
lem-F1-CS-K1-part24 : Ws → ⟪ (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ Toff203 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ X0 ∷ K2⁻ ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ
lem-F1-CS-K1-part24 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (run b42))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ Toff203 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ K2 ∷ CCZ124 ∷ K2⁻ ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ K2⁻ ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b0 = at 42 1 (CS02 ∷ []) (refl) ▸
       at 41 4 (Toff203 ∷ X0 ∷ CS02 ∷ X0 ∷ []) (sym (wl0572 (lit c4))) ▸
       at 43 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 41 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 38 0 (K2 ∷ K2⁻ ∷ []) (sym (wl0579 (lit c4))) ▸
       at 43 0 (K2 ∷ K2⁻ ∷ []) (sym (wl0579 (lit c4))) ▸
       at 48 0 (K2 ∷ K2⁻ ∷ []) (sym (wl0579 (lit c4))) ▸
       at 39 5 (CCZ124 ∷ []) (sym (wp0245 c4)) ▸ done

  b1 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ K2 ∷ CCZ124 ∷ K2⁻ ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ K2⁻ ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ Toff203 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b1 = at 40 5 (CCZ023 ∷ []) (sym (wl0580 (lit c4))) ▸
       at 39 2 (CCZ023 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at0112243043 c4) ▸
       at 39 1 (K2⁻ ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ []) (wl0580 (lit c4)) ▸
       at 44 1 (K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ []) (wp0245 c4) ▸
       at 38 2 [] (wl0579 (lit c4)) ▸
       at 41 2 [] (wl0579 (lit c4)) ▸
       at 44 2 [] (wl0579 (lit c4)) ▸
       at 38 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸ done

  b2 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ Toff203 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Toff304 ∷ X0 ∷ X0 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b2 = at 38 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 39 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl0581 (lit c4)) ▸
       at 40 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 43 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 46 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 49 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 36 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4) ▸
       at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b3 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ Toff304 ∷ X0 ∷ X0 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b3 = at 40 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 43 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 44 6 (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0582 (lit c4))) ▸
       at 41 6 (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff304 ∷ X0 ∷ []) (sym (wp0246 c4)) ▸
       at 38 6 (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0582 (lit c4))) ▸
       at 35 6 (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff304 ∷ X0 ∷ []) (sym (wp0246 c4)) ▸
       at 40 2 [] (wl0509 (lit c4)) ▸
       at 41 2 [] (wl0509 (lit c4)) ▸ done

  b4 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b4 = at 42 2 [] (wl0509 (lit c4)) ▸
       at 39 4 (Bx3-0412 ∷ []) (sym (lem-beta-T-at0310243142 c4)) ▸
       at 39 1 (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4) ▸
       at 39 1 (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4) ▸
       at 39 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03103441 c4) ▸
       at 40 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 43 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 46 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b5 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ X0 ∷ K2⁻ ∷ CCZ134 ∷ X0 ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b5 = at 49 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 48 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 47 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 50 2 (CX20 ∷ X0 ∷ []) (sym (wl0583 (lit c4))) ▸
       at 49 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸
       at 48 2 (CX20 ∷ X0 ∷ []) (sym (wl0583 (lit c4))) ▸
       at 51 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 50 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸ done

  b6 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ X0 ∷ K2⁻ ∷ CCZ134 ∷ X0 ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b6 = at 49 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 52 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 51 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 50 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 51 4 (CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (sym (wp0247 c4)) ▸
       at 54 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 53 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 52 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸ done

  b7 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ X0 ∷ K2⁻ ∷ CCZ134 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b7 = at 55 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 54 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 53 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 56 2 (CX20 ∷ X0 ∷ []) (sym (wl0583 (lit c4))) ▸
       at 55 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸
       at 54 2 (CX20 ∷ X0 ∷ []) (sym (wl0583 (lit c4))) ▸
       at 57 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 56 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸ done

  b8 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ X0 ∷ K2⁻ ∷ CCZ134 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ X0 ∷ CCZ134 ∷ K2⁻ ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b8 = at 55 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 58 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 57 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 56 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 59 2 (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑)) ▸
       at 58 2 (CS23 ∷ CCZ134 ∷ []) (wl0558 (lit c4)) ▸
       at 57 2 (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑)) ▸
       at 60 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸ done

  b9 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ X0 ∷ CCZ134 ∷ K2⁻ ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ X0 ∷ CX20 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b9 = at 59 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 58 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 44 15 (K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (sym (wl0584 (lit c4))) ▸
       at 43 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 42 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 41 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 44 2 (CX20 ∷ X0 ∷ []) (sym (wl0583 (lit c4))) ▸
       at 43 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸ done

  b10 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ X0 ∷ CX20 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b10 = at 42 2 (CX20 ∷ X0 ∷ []) (sym (wl0583 (lit c4))) ▸
       at 45 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 44 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 43 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 46 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 45 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 44 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 45 4 (CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (sym (wp0247 c4)) ▸ done

  b11 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ X0 ∷ CX20 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b11 = at 48 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 47 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 46 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 49 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 48 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 47 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 50 2 (CX20 ∷ X0 ∷ []) (sym (wl0583 (lit c4))) ▸
       at 49 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸ done

  b12 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ X0 ∷ CX20 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ X0 ∷ CCZ134 ∷ CS23 ∷ X0 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b12 = at 48 2 (CX20 ∷ X0 ∷ []) (sym (wl0583 (lit c4))) ▸
       at 51 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 50 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 49 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 52 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 51 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 50 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 53 2 (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑)) ▸ done

  b13 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ X0 ∷ CCZ134 ∷ CS23 ∷ X0 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b13 = at 52 2 (CS23 ∷ CCZ134 ∷ []) (wl0558 (lit c4)) ▸
       at 51 2 (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑)) ▸
       at 54 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 53 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 52 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 38 15 (K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (sym (wl0584 (lit c4))) ▸
       at 52 2 [] (wl0509 (lit c4)) ▸
       at 53 2 [] (wl0509 (lit c4)) ▸ done

  b14 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b14 = at 54 2 [] (wl0509 (lit c4)) ▸
       at 51 4 (Bx3-0241 ∷ []) (sym (lem-beta-T-at03103441 c4)) ▸
       at 51 1 (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4) ▸
       at 51 1 (Bx3-0412 ∷ []) (lem-sym34-at0310243241 c4) ▸
       at 37 2 [] (wl0550 (lit c4)) ▸
       at 38 2 [] (wl0550 (lit c4)) ▸
       at 39 2 [] (wl0550 (lit c4)) ▸
       at 40 2 [] (wl0550 (lit c4)) ▸ done

  b15 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b15 = at 36 5 (CCZ023 ∷ []) (sym (wl0581 (lit c4))) ▸
       at 35 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 38 2 [] (wl0509 (lit c4)) ▸
       at 39 2 [] (wl0509 (lit c4)) ▸
       at 40 2 [] (wl0509 (lit c4)) ▸
       at 41 2 [] (wl0509 (lit c4)) ▸
       at 37 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 37 1 (Sb2-0-41-3 ∷ []) (sym (lem-F0 c4)) ▸ done

  b16 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CCZ124 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b16 = at 38 2 (CCZ124 ∷ X0 ∷ []) (sym (wp0225 c4)) ▸
       at 37 2 (CCZ124 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0210243143 c4) ▸
       at 36 2 (CCZ124 ∷ X0 ∷ []) (sym (wp0225 c4)) ▸
       at 33 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 33 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 33 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 33 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 29 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸ done

  b17 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b17 = at 29 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 29 1 (CS03 ∷ []) (refl) ▸
       at 26 4 (CS03 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl0585 (lit c4))) ▸
       at 26 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 31 1 (CS03⁻ ∷ []) (refl) ▸
       at 27 6 (Toff314 ∷ CS03⁻ ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wp0248 c4)) ▸
       at 28 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 33 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸ done

  b18 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X0 ∷ CK01 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b18 = at 33 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 33 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 30 4 (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl0514 (lit c4))) ▸
       at 33 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 32 2 (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ)) ▸
       at 31 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 32 4 (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl0514 (lit c4))) ▸
       at 35 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸ done

  b19 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X0 ∷ CK01 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b19 = at 34 2 (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ)) ▸
       at 33 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 30 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 30 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 30 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 26 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 26 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 26 1 (CS03 ∷ []) (refl) ▸ done

  b20 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b20 = at 24 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 25 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 36 1 (CS03⁻ ∷ []) (refl) ▸
       at 35 4 (CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0531 (lit c4))) ▸
       at 37 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b21 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b21 = at 30 1 (CS03 ∷ []) (refl) ▸
       at 26 10 (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0204 c4)) ▸
       at 31 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 24 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 25 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 4 (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0530 (lit c4))) ▸ done

  b22 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS03 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b22 = at 29 4 (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0203 c4)) ▸
       at 26 4 (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 23 4 (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0203 c4)) ▸
       at 26 2 [] (wl0509 (lit c4)) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 25 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 26 2 [] (wl0509 (lit c4)) ▸ done

  b23 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS03 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b23 = at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 25 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 23 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 26 2 (Toff314 ∷ X0 ∷ []) (sym (wp0202 c4)) ▸
       at 25 2 (Toff314 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4) ▸
       at 24 2 (Toff314 ∷ X0 ∷ []) (sym (wp0202 c4)) ▸ done

  b24 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b24 = at 28 1 (CS03⁻ ∷ []) (refl) ▸
       at 26 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 27 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 30 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 33 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 36 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 38 1 (CS03⁻ ∷ []) (refl) ▸
       at 37 4 (CS03⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0529 (lit c4))) ▸ done

  b25 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b25 = at 39 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 32 1 (CS03 ∷ []) (refl) ▸
       at 28 10 (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0201 c4)) ▸
       at 33 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 26 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 27 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 30 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 33 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b26 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b26 = at 34 4 (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 31 4 (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0200 c4)) ▸
       at 28 4 (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 25 4 (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0200 c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 27 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸ done

  b27 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb2-0-41-3 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b27 = at 28 2 [] (wl0509 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸
       at 27 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 25 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 28 2 (Toff314 ∷ X0 ∷ []) (sym (wp0202 c4)) ▸
       at 27 2 (Toff314 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4) ▸ done

  b28 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Toff314 ∷ Sb2-0-41-3 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b28 = at 26 2 (Toff314 ∷ X0 ∷ []) (sym (wp0202 c4)) ▸
       at 30 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 30 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 30 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 30 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 28 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 28 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b29 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ K2 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b29 = at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 40 1 (CS02⁻ ∷ []) (refl) ▸
       at 39 4 (Toff203 ∷ X0 ∷ CS02⁻ ∷ X0 ∷ []) (sym (wl0571 (lit c4))) ▸
       at 41 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 39 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 36 0 (K2 ∷ K2⁻ ∷ []) (sym (wl0579 (lit c4))) ▸ done

  b30 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ K2 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ K2⁻ ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b30 = at 41 0 (K2 ∷ K2⁻ ∷ []) (sym (wl0579 (lit c4))) ▸
       at 46 0 (K2 ∷ K2⁻ ∷ []) (sym (wl0579 (lit c4))) ▸
       at 37 5 (CCZ124 ∷ []) (sym (wp0245 c4)) ▸
       at 38 5 (CCZ023 ∷ []) (sym (wl0580 (lit c4))) ▸
       at 37 2 (CCZ023 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at0112243043 c4) ▸
       at 37 1 (K2⁻ ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ []) (wl0580 (lit c4)) ▸
       at 42 1 (K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ []) (wp0245 c4) ▸
       at 36 2 [] (wl0579 (lit c4)) ▸ done

  b31 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ K2⁻ ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ K2 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b31 = at 39 2 [] (wl0579 (lit c4)) ▸
       at 42 2 [] (wl0579 (lit c4)) ▸
       at 36 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 34 1 (CS02 ∷ []) (refl) ▸
       at 33 4 (Toff203 ∷ X0 ∷ CS02 ∷ X0 ∷ []) (sym (wl0572 (lit c4))) ▸
       at 35 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 33 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 30 0 (K2 ∷ K2⁻ ∷ []) (sym (wl0579 (lit c4))) ▸ done

  b32 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ K2 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ K2⁻ ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b32 = at 35 0 (K2 ∷ K2⁻ ∷ []) (sym (wl0579 (lit c4))) ▸
       at 40 0 (K2 ∷ K2⁻ ∷ []) (sym (wl0579 (lit c4))) ▸
       at 31 5 (CCZ124 ∷ []) (sym (wp0245 c4)) ▸
       at 32 5 (CCZ023 ∷ []) (sym (wl0580 (lit c4))) ▸
       at 31 2 (CCZ023 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at0112243043 c4) ▸
       at 31 1 (K2⁻ ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ []) (wl0580 (lit c4)) ▸
       at 36 1 (K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ []) (wp0245 c4) ▸
       at 30 2 [] (wl0579 (lit c4)) ▸ done

  b33 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ K2 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ K2⁻ ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b33 = at 33 2 [] (wl0579 (lit c4)) ▸
       at 36 2 [] (wl0579 (lit c4)) ▸
       at 30 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 30 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 31 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl0581 (lit c4)) ▸
       at 32 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 35 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 38 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸ done

  b34 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Bx3-0412 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Toff304 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff304 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b34 = at 41 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 28 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 36 6 (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0582 (lit c4))) ▸
       at 33 6 (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff304 ∷ X0 ∷ []) (sym (wp0246 c4)) ▸
       at 30 6 (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0582 (lit c4))) ▸ done

  b35 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Toff304 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff304 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b35 = at 27 6 (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff304 ∷ X0 ∷ []) (sym (wp0246 c4)) ▸
       at 32 2 [] (wl0509 (lit c4)) ▸
       at 33 2 [] (wl0509 (lit c4)) ▸
       at 34 2 [] (wl0509 (lit c4)) ▸
       at 31 4 (Bx3-0412 ∷ []) (sym (lem-beta-T-at0310243142 c4)) ▸
       at 31 1 (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4) ▸
       at 31 1 (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4) ▸
       at 31 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03103441 c4) ▸ done

  b36 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ X0 ∷ CX20 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b36 = at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 41 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 40 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 39 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 42 2 (CX20 ∷ X0 ∷ []) (sym (wl0583 (lit c4))) ▸
       at 41 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸ done

  b37 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ X0 ∷ CX20 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b37 = at 40 2 (CX20 ∷ X0 ∷ []) (sym (wl0583 (lit c4))) ▸
       at 43 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 42 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 41 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 44 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 43 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 42 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 43 4 (CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (sym (wp0247 c4)) ▸ done

  b38 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ X0 ∷ CX20 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b38 = at 46 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 45 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 44 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 47 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 46 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 45 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 48 2 (CX20 ∷ X0 ∷ []) (sym (wl0583 (lit c4))) ▸
       at 47 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸ done

  b39 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ X0 ∷ CX20 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ X0 ∷ CCZ134 ∷ CS23 ∷ X0 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b39 = at 46 2 (CX20 ∷ X0 ∷ []) (sym (wl0583 (lit c4))) ▸
       at 49 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 48 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 47 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 50 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 49 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 48 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 51 2 (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑)) ▸ done

  b40 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ X0 ∷ CCZ134 ∷ CS23 ∷ X0 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ K2 ∷ CCZ134 ∷ X0 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b40 = at 50 2 (CS23 ∷ CCZ134 ∷ []) (wl0558 (lit c4)) ▸
       at 49 2 (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑)) ▸
       at 52 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 51 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 50 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 36 15 (K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (sym (wl0584 (lit c4))) ▸
       at 35 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 34 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸ done

  b41 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ K2 ∷ CCZ134 ∷ X0 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ X0 ∷ CCZ134 ∷ K2 ∷ X0 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b41 = at 33 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 36 2 (CX20 ∷ X0 ∷ []) (sym (wl0583 (lit c4))) ▸
       at 35 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸
       at 34 2 (CX20 ∷ X0 ∷ []) (sym (wl0583 (lit c4))) ▸
       at 37 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 36 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 35 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 38 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸ done

  b42 : Chain (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ X0 ∷ CCZ134 ∷ K2 ∷ X0 ∷ CS03⁻ ∷ K2⁻ ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS03⁻ ∷ X0 ∷ K2⁻ ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX20 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b42 = at 37 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 36 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 37 4 (CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (sym (wp0247 c4)) ▸
       at 40 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 39 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸ done

