{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D097 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0404 ; wl0509 ; wl0510 ; wl0511 ; wl0512 ; wl0528 ; wl0530 ; wl0535 ; wl0544 ; wl0545 ; wl0546 ; wl0547 ; wl0548 ; wl0549 ; wl0550 ; wl0551 ; wl0552 ; wl0553 ; wl0554 ; wl0555 ; wl0556 ; wl0557 ; wl0558 ; wl0559 ; wl0560 ; wl0561 ; wl0562 ; wl0563 ; wl0564 ; wl0565 ; wp0190 ; wp0191 ; wp0200 ; wp0202 ; wp0203 ; wp0212 ; wp0213 ; wp0214 ; wp0215 ; wp0216 ; wp0217 ; wp0218 ; wp0219)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0d)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-BOXd-BOX-at0310243142 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 ; lem-beta-T-at03103441 ; lem-sym23-at0310243241 ; lem-sym23-at03103441 ; lem-sym34-at0310243142 ; lem-sym34-at0310243241)
-- F1 CS-K1 [rhs shape] part6: 333 steps
lem-F1-CS-K1-rhs-shape-part6 : Ws → ⟪ (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ X0 ∷ CS12 ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS12⁻ ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-rhs-shape-part6 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (run b41)))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b0 = at 43 2 [] (wl0509 (lit c4)) ▸
       at 39 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 39 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 40 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 43 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 46 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 49 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 51 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸ done

  b1 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b1 = at 51 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 52 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 55 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 58 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 59 4 (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0510 (lit c4))) ▸
       at 56 4 (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0190 c4)) ▸
       at 53 4 (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0510 (lit c4))) ▸
       at 50 4 (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0190 c4)) ▸ done

  b2 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b2 = at 53 2 [] (wl0509 (lit c4)) ▸
       at 54 2 [] (wl0509 (lit c4)) ▸
       at 55 2 [] (wl0509 (lit c4)) ▸
       at 52 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 52 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 47 4 (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0191 c4)) ▸
       at 45 1 (CS03⁻ ∷ []) (refl) ▸
       at 44 4 (S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0512 (lit c4))) ▸ done

  b3 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b3 = at 46 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 41 4 (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0191 c4)) ▸
       at 39 1 (CS03 ∷ []) (refl) ▸
       at 38 4 (S0 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0511 (lit c4))) ▸
       at 40 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 41 2 [] (wl0509 (lit c4)) ▸
       at 42 2 [] (wl0509 (lit c4)) ▸
       at 43 2 [] (wl0509 (lit c4)) ▸ done

  b4 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b4 = at 44 2 [] (wl0509 (lit c4)) ▸
       at 40 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 41 2 (ι⁻ ∷ X0 ∷ []) (zc⁻) ▸
       at 40 2 (ι⁻ ∷ Sb⁻2-0-41-3 ∷ []) (zc⁻) ▸
       at 39 2 (ι⁻ ∷ X0 ∷ []) (zc⁻) ▸
       at 33 7 (CK01⁻ ∷ []) (sym (wl0535 (lit c4))) ▸
       at 46 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 46 1 (CS03 ∷ []) (refl) ▸ done

  b5 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b5 = at 43 4 (CS03 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (sym (wl0544 (lit c4))) ▸
       at 43 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 48 1 (CS03⁻ ∷ []) (refl) ▸
       at 44 6 (Toff314 ∷ CS03⁻ ∷ Toff314 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (sym (wp0212 c4)) ▸
       at 45 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 50 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 50 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 50 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸ done

  b6 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b6 = at 47 4 (Toff201 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (sym (wl0545 (lit c4))) ▸
       at 50 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 49 2 (CCZ234 ∷ CK01⁻ ∷ []) (c₂ (S • CK₀₁) (CCZ)) ▸
       at 48 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 49 4 (Toff201 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (sym (wl0545 (lit c4))) ▸
       at 52 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 51 2 (CCZ234 ∷ CK01⁻ ∷ []) (c₂ (S • CK₀₁) (CCZ)) ▸
       at 50 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸ done

  b7 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b7 = at 47 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 47 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 47 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 43 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 43 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 43 1 (CS03 ∷ []) (refl) ▸
       at 41 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 42 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b8 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b8 = at 45 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 48 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 51 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 53 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 53 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 54 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 57 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 60 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b9 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b9 = at 61 4 (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 58 4 (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0203 c4)) ▸
       at 55 4 (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 52 4 (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0203 c4)) ▸
       at 55 2 [] (wl0509 (lit c4)) ▸
       at 56 2 [] (wl0509 (lit c4)) ▸
       at 57 2 [] (wl0509 (lit c4)) ▸
       at 54 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸ done

  b10 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b10 = at 54 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 47 1 (CS03⁻ ∷ []) (refl) ▸
       at 43 10 (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0213 c4)) ▸
       at 48 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 41 1 (CS03 ∷ []) (refl) ▸
       at 40 4 (CS03 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0546 (lit c4))) ▸
       at 42 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 43 2 [] (wl0509 (lit c4)) ▸ done

  b11 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b11 = at 44 2 [] (wl0509 (lit c4)) ▸
       at 45 2 [] (wl0509 (lit c4)) ▸
       at 46 2 [] (wl0509 (lit c4)) ▸
       at 42 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 40 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 43 2 (Toff314 ∷ X0 ∷ []) (sym (wp0202 c4)) ▸
       at 42 2 (Toff314 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4) ▸
       at 41 2 (Toff314 ∷ X0 ∷ []) (sym (wp0202 c4)) ▸ done

  b12 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b12 = at 45 1 (CS03⁻ ∷ []) (refl) ▸
       at 43 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 44 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 47 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 50 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 53 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 55 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 55 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸ done

  b13 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b13 = at 56 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 59 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 62 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 63 4 (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 60 4 (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0200 c4)) ▸
       at 57 4 (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 54 4 (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0200 c4)) ▸
       at 57 2 [] (wl0509 (lit c4)) ▸ done

  b14 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b14 = at 58 2 [] (wl0509 (lit c4)) ▸
       at 59 2 [] (wl0509 (lit c4)) ▸
       at 56 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 56 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 49 1 (CS03⁻ ∷ []) (refl) ▸
       at 45 10 (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0214 c4)) ▸
       at 50 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 43 1 (CS03 ∷ []) (refl) ▸ done

  b15 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ CS03 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b15 = at 42 4 (CS03⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 44 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 45 2 [] (wl0509 (lit c4)) ▸
       at 46 2 [] (wl0509 (lit c4)) ▸
       at 47 2 [] (wl0509 (lit c4)) ▸
       at 48 2 [] (wl0509 (lit c4)) ▸
       at 44 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 42 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b16 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb⁻3-0-41-2 ∷ X0 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b16 = at 45 2 (Toff314 ∷ X0 ∷ []) (sym (wp0202 c4)) ▸
       at 44 2 (Toff314 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4) ▸
       at 43 2 (Toff314 ∷ X0 ∷ []) (sym (wp0202 c4)) ▸
       at 47 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 47 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 47 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 47 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 45 1 (Sb⁻3-0-41-2 ∷ []) (lem-F0d c4) ▸ done

  b17 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb⁻3-0-41-2 ∷ X0 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b17 = at 45 1 (Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) (refl) ▸
       at 46 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 49 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 52 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 55 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 59 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 60 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0549 (lit c4)) ▸
       at 61 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸ done

  b18 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b18 = at 64 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 67 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 70 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 57 1 (Bx3-0412 ∷ []) (lem-BOXd-BOX-at0310243142 c4) ▸
       at 57 1 (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4) ▸
       at 57 1 (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4) ▸
       at 57 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03103441 c4) ▸
       at 58 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b19 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ X0 ∷ CS13 ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ X0 ∷ CS02 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b19 = at 61 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 64 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 67 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 66 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 65 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 67 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4)) ▸
       at 68 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 71 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b20 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ X0 ∷ CS13 ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ X0 ∷ CS02 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CS02 ∷ X0 ∷ CS13 ∷ CX41 ∷ X0 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS34 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b20 = at 74 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 77 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 78 4 (CS02 ∷ X0 ∷ CS34 ∷ X0 ∷ []) (sym (wp0215 c4)) ▸
       at 75 4 (CS02 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (sym (wp0216 c4)) ▸
       at 72 4 (CS02 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) (sym (wl0552 (lit c4))) ▸
       at 69 4 (CS02 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (sym (wp0216 c4)) ▸
       at 66 4 (CS02 ∷ X0 ∷ CS13 ∷ X0 ∷ []) (sym (wl0553 (lit c4))) ▸
       at 69 2 [] (wl0509 (lit c4)) ▸ done

  b21 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CS02 ∷ X0 ∷ CS13 ∷ CX41 ∷ X0 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS34 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b21 = at 70 2 [] (wl0509 (lit c4)) ▸
       at 71 2 [] (wl0509 (lit c4)) ▸
       at 72 2 [] (wl0509 (lit c4)) ▸
       at 68 5 (CCZ134 ∷ []) (sym (wl0404 (lit c4))) ▸
       at 69 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 68 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 67 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 62 6 (K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (sym (wl0555 (lit c4))) ▸ done

  b22 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ X0 ∷ CS13 ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS34 ∷ X0 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b22 = at 61 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 60 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 59 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 61 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4)) ▸
       at 62 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 65 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 68 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 71 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b23 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ X0 ∷ CS13 ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS34 ∷ X0 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CS02 ∷ X0 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X0 ∷ X0 ∷ CS34 ∷ X0 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b23 = at 72 4 (CS02 ∷ X0 ∷ CS34 ∷ X0 ∷ []) (sym (wp0215 c4)) ▸
       at 69 4 (CS02 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (sym (wp0216 c4)) ▸
       at 66 4 (CS02 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) (sym (wl0552 (lit c4))) ▸
       at 63 4 (CS02 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (sym (wp0216 c4)) ▸
       at 60 4 (CS02 ∷ X0 ∷ CS13 ∷ X0 ∷ []) (sym (wl0553 (lit c4))) ▸
       at 63 2 [] (wl0509 (lit c4)) ▸
       at 64 2 [] (wl0509 (lit c4)) ▸
       at 65 2 [] (wl0509 (lit c4)) ▸ done

  b24 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CS02 ∷ X0 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X0 ∷ X0 ∷ CS34 ∷ X0 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b24 = at 66 2 [] (wl0509 (lit c4)) ▸
       at 62 5 (CCZ134 ∷ []) (sym (wl0404 (lit c4))) ▸
       at 63 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 62 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 61 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 56 6 (K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (sym (wl0555 (lit c4))) ▸
       at 61 2 [] (wl0509 (lit c4)) ▸
       at 62 2 [] (wl0509 (lit c4)) ▸ done

  b25 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Bx3-0241 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b25 = at 63 2 [] (wl0509 (lit c4)) ▸
       at 60 4 (Bx3-0241 ∷ []) (sym (lem-beta-T-at03103441 c4)) ▸
       at 60 1 (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4) ▸
       at 60 1 (Bx3-0412 ∷ []) (lem-sym34-at0310243241 c4) ▸
       at 60 1 (Bx⁻3-0412 ∷ []) (sym (lem-BOXd-BOX-at0310243142 c4)) ▸
       at 60 1 (Bx3-0412 ∷ []) (lem-BOXd-BOX-at0310243142 c4) ▸
       at 60 1 (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4) ▸
       at 60 1 (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4) ▸ done

  b26 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Bx3-0241 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b26 = at 60 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03103441 c4) ▸
       at 61 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 64 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 67 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 70 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 69 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 68 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 69 4 (CX30 ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (sym (wp0217 c4)) ▸ done

  b27 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ X0 ∷ CS13 ∷ X0 ∷ X0 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ X0 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b27 = at 72 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 71 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 70 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 73 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 72 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 71 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 73 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4)) ▸
       at 74 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b28 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ X0 ∷ CS13 ∷ X0 ∷ X0 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ X0 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ X0 ∷ CS13 ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS34 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b28 = at 77 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 80 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 83 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 84 4 (CS02⁻ ∷ X0 ∷ CS34 ∷ X0 ∷ []) (sym (wp0218 c4)) ▸
       at 81 4 (CS02⁻ ∷ X0 ∷ CX41 ∷ X0 ∷ []) (sym (wp0219 c4)) ▸
       at 78 4 (CS02⁻ ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) (sym (wl0556 (lit c4))) ▸
       at 75 4 (CS02⁻ ∷ X0 ∷ CX41 ∷ X0 ∷ []) (sym (wp0219 c4)) ▸
       at 72 4 (CS02⁻ ∷ X0 ∷ CS13 ∷ X0 ∷ []) (sym (wl0557 (lit c4))) ▸ done

  b29 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ X0 ∷ CS13 ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS34 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b29 = at 75 2 [] (wl0509 (lit c4)) ▸
       at 76 2 [] (wl0509 (lit c4)) ▸
       at 77 2 [] (wl0509 (lit c4)) ▸
       at 78 2 [] (wl0509 (lit c4)) ▸
       at 74 5 (CCZ134 ∷ []) (sym (wl0404 (lit c4))) ▸
       at 75 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 74 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 73 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸ done

  b30 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ X0 ∷ CCZ134 ∷ K2 ∷ X0 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b30 = at 76 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 75 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 74 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 75 4 (CX30 ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (sym (wp0217 c4)) ▸
       at 78 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 77 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 76 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 79 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸ done

  b31 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ X0 ∷ CCZ134 ∷ K2 ∷ X0 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b31 = at 78 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 77 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 80 2 (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑)) ▸
       at 79 2 (CS23 ∷ CCZ134 ∷ []) (wl0558 (lit c4)) ▸
       at 78 2 (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑)) ▸
       at 81 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 80 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 79 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸ done

  b32 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b32 = at 65 15 (K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (sym (wl0559 (lit c4))) ▸
       at 64 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 63 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 62 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 63 4 (CX30 ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (sym (wp0217 c4)) ▸
       at 66 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 65 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 64 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸ done

  b33 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ X0 ∷ CS13 ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS34 ∷ X0 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b33 = at 67 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 66 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 65 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 67 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4)) ▸
       at 68 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 71 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 74 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 77 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b34 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ X0 ∷ CS13 ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS34 ∷ X0 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ X0 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X0 ∷ X0 ∷ CS34 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b34 = at 78 4 (CS02⁻ ∷ X0 ∷ CS34 ∷ X0 ∷ []) (sym (wp0218 c4)) ▸
       at 75 4 (CS02⁻ ∷ X0 ∷ CX41 ∷ X0 ∷ []) (sym (wp0219 c4)) ▸
       at 72 4 (CS02⁻ ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) (sym (wl0556 (lit c4))) ▸
       at 69 4 (CS02⁻ ∷ X0 ∷ CX41 ∷ X0 ∷ []) (sym (wp0219 c4)) ▸
       at 66 4 (CS02⁻ ∷ X0 ∷ CS13 ∷ X0 ∷ []) (sym (wl0557 (lit c4))) ▸
       at 69 2 [] (wl0509 (lit c4)) ▸
       at 70 2 [] (wl0509 (lit c4)) ▸
       at 71 2 [] (wl0509 (lit c4)) ▸ done

  b35 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ X0 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X0 ∷ X0 ∷ CS34 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b35 = at 72 2 [] (wl0509 (lit c4)) ▸
       at 68 5 (CCZ134 ∷ []) (sym (wl0404 (lit c4))) ▸
       at 69 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 68 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 67 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 70 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 69 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 68 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸ done

  b36 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ X0 ∷ CCZ134 ∷ CS23 ∷ X0 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b36 = at 69 4 (CX30 ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (sym (wp0217 c4)) ▸
       at 72 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 71 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 70 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 73 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 72 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 71 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 74 2 (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑)) ▸ done

  b37 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ X0 ∷ CCZ134 ∷ CS23 ∷ X0 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b37 = at 73 2 (CS23 ∷ CCZ134 ∷ []) (wl0558 (lit c4)) ▸
       at 72 2 (CS23 ∷ X0 ∷ []) (c₁ (X) (CS ↑)) ▸
       at 75 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 74 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 73 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 59 15 (K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (sym (wl0559 (lit c4))) ▸
       at 73 2 [] (wl0509 (lit c4)) ▸
       at 74 2 [] (wl0509 (lit c4)) ▸ done

  b38 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b38 = at 75 2 [] (wl0509 (lit c4)) ▸
       at 72 4 (Bx3-0241 ∷ []) (sym (lem-beta-T-at03103441 c4)) ▸
       at 72 1 (Bx3-0421 ∷ []) (lem-sym23-at03103441 c4) ▸
       at 72 1 (Bx3-0412 ∷ []) (lem-sym34-at0310243241 c4) ▸
       at 72 1 (Bx⁻3-0412 ∷ []) (sym (lem-BOXd-BOX-at0310243142 c4)) ▸
       at 58 2 [] (wl0550 (lit c4)) ▸
       at 59 2 [] (wl0550 (lit c4)) ▸
       at 60 2 [] (wl0550 (lit c4)) ▸ done

  b39 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ K2 ∷ CX03 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b39 = at 61 2 [] (wl0550 (lit c4)) ▸
       at 57 5 (CCZ023 ∷ []) (sym (wl0549 (lit c4))) ▸
       at 56 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 56 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 57 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 58 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 61 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 64 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸ done

  b40 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ K2 ∷ CX03 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ X0 ∷ CCZ124 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b40 = at 67 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 55 4 (K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ []) (sym (wl0561 (lit c4))) ▸
       at 54 4 (K2 ∷ CS23 ∷ K2⁻ ∷ Toff214 ∷ []) (sym (wl0562 (lit c4))) ▸
       at 53 4 (K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ []) (sym (wl0561 (lit c4))) ▸
       at 57 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (sym (wl0563 (lit c4))) ▸
       at 58 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 61 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 62 6 (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2⁻ ∷ X0 ∷ []) (sym (wl0564 (lit c4))) ▸ done

  b41 : Chain (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ X0 ∷ CCZ124 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ K2 ∷ CS23 ∷ K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ X0 ∷ CS12 ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS12⁻ ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CS23⁻ ∷ K2⁻ ∷ K2 ∷ CX03 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b41 = at 60 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0565 (lit c4)) ▸
       at 61 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 64 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 67 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 70 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

