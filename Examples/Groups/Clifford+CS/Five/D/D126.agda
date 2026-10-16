{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D126 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0393 ; wl0404 ; wl0433 ; wl0509 ; wl0510 ; wl0511 ; wl0512 ; wl0528 ; wl0530 ; wl0533 ; wl0534 ; wl0535 ; wl0536 ; wl0537 ; wl0538 ; wl0539 ; wl0540 ; wl0541 ; wl0542 ; wl0543 ; wl0544 ; wl0545 ; wl0546 ; wl0547 ; wl0548 ; wl0549 ; wl0550 ; wl0551 ; wl0552 ; wl0553 ; wl0554 ; wl0555 ; wp0182 ; wp0183 ; wp0184 ; wp0185 ; wp0186 ; wp0187 ; wp0188 ; wp0189 ; wp0190 ; wp0191 ; wp0200 ; wp0202 ; wp0203 ; wp0206 ; wp0207 ; wp0208 ; wp0209 ; wp0210 ; wp0211 ; wp0212 ; wp0213 ; wp0214 ; wp0215 ; wp0216)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F0d)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443 ; lem-beta-T-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D090 using (lem-BOXd-BOX-at0310243142 ; lem-F5d-CS01-at0440 ; lem-SBtgtd-at0440 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 ; lem-beta-T-at03103441 ; lem-sym23-at0310243241 ; lem-sym34-at0310243142)
-- F1 CS-K1 part2: 404 steps
lem-F1-CS-K1-part2 : Ws → ⟪ (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ K2 ∷ X0 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) ⟫ʷ
lem-F1-CS-K1-part2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (run b50))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b0 = at 26 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 23 4 (X0 ∷ CS23 ∷ X0 ∷ CS04⁻ ∷ []) (wp0183 c4) ▸
       at 26 4 (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) (wp0184 c4) ▸
       at 29 4 (X0 ∷ CS23⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0185 c4) ▸
       at 32 4 (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) (wp0184 c4) ▸ done

  b1 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b1 = at 35 4 (X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ []) (wp0186 c4) ▸
       at 25 2 [] (wl0509 (lit c4)) ▸
       at 26 2 [] (wl0509 (lit c4)) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 24 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 26 4 (X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ []) (wp0182 c4) ▸
       at 31 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸ done

  b2 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b2 = at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 41 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 29 4 (X0 ∷ CS23 ∷ X0 ∷ CS04⁻ ∷ []) (wp0183 c4) ▸
       at 32 4 (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) (wp0184 c4) ▸
       at 35 4 (X0 ∷ CS23⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0185 c4) ▸
       at 38 4 (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) (wp0184 c4) ▸ done

  b3 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS12 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b3 = at 41 4 (X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ []) (wp0186 c4) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸
       at 32 2 [] (wl0509 (lit c4)) ▸
       at 33 2 [] (wl0509 (lit c4)) ▸
       at 34 2 [] (wl0509 (lit c4)) ▸
       at 30 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 22 2 [] (wl0509 (lit c4)) ▸
       at 23 2 [] (wl0509 (lit c4)) ▸ done

  b4 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b4 = at 24 2 [] (wl0509 (lit c4)) ▸
       at 21 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 23 4 (X0 ∷ Toff314 ∷ X0 ∷ CS04⁻ ∷ []) (wp0187 c4) ▸
       at 28 1 (CS03 ∷ []) (refl) ▸
       at 26 4 (X0 ∷ CS03 ∷ X0 ∷ CS04⁻ ∷ []) (wp0188 c4) ▸
       at 27 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 29 4 (X0 ∷ Toff314 ∷ X0 ∷ CS04⁻ ∷ []) (wp0187 c4) ▸
       at 34 1 (CS03⁻ ∷ []) (refl) ▸ done

  b5 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b5 = at 32 4 (X0 ∷ CS03⁻ ∷ X0 ∷ CS04⁻ ∷ []) (wp0189 c4) ▸
       at 33 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 22 2 [] (wl0509 (lit c4)) ▸
       at 23 2 [] (wl0509 (lit c4)) ▸
       at 24 2 [] (wl0509 (lit c4)) ▸
       at 25 2 [] (wl0509 (lit c4)) ▸
       at 21 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 21 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b6 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b6 = at 22 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 25 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 21 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 22 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 25 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b7 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b7 = at 19 4 (X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ []) (wp0190 c4) ▸
       at 22 4 (X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ []) (wl0510 (lit c4)) ▸
       at 25 4 (X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ []) (wp0190 c4) ▸
       at 28 4 (X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ []) (wl0510 (lit c4)) ▸
       at 21 2 [] (wl0509 (lit c4)) ▸
       at 22 2 [] (wl0509 (lit c4)) ▸
       at 23 2 [] (wl0509 (lit c4)) ▸
       at 20 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸ done

  b8 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b8 = at 22 4 (X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ []) (wp0191 c4) ▸
       at 27 1 (CS03 ∷ []) (refl) ▸
       at 25 4 (X0 ∷ CS03 ∷ X0 ∷ S0 ∷ []) (wl0511 (lit c4)) ▸
       at 26 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 28 4 (X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ []) (wp0191 c4) ▸
       at 33 1 (CS03⁻ ∷ []) (refl) ▸
       at 31 4 (X0 ∷ CS03⁻ ∷ X0 ∷ S0 ∷ []) (wl0512 (lit c4)) ▸
       at 32 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b9 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ K1⁻ ∷ CS14⁻ ∷ K1⁻ ∷ CS14⁻ ∷ S4 ∷ ι⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b9 = at 21 2 [] (wl0509 (lit c4)) ▸
       at 22 2 [] (wl0509 (lit c4)) ▸
       at 23 2 [] (wl0509 (lit c4)) ▸
       at 24 2 [] (wl0509 (lit c4)) ▸
       at 20 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 30 1 (CS14⁻ ∷ K1⁻ ∷ CS14⁻ ∷ K1⁻ ∷ CS14⁻ ∷ S4 ∷ ι1⁻ ∷ []) (wp0206 c4) ▸
       at 36 1 (ι⁻ ∷ []) (uₛ ((iI • iI • iI) ↑) (iI • iI • iI) Eq.refl) ▸
       at 30 1 (Sb⁻2-4-01-3 ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ []) (lem-F5d-CS01-at0440 c4) ▸ done

  b10 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ K1⁻ ∷ CS14⁻ ∷ K1⁻ ∷ CS14⁻ ∷ S4 ∷ ι⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ S4 ∷ ι⁻ ∷ S4⁻ ∷ CS14 ∷ [])
  b10 = at 30 1 (Sb⁻2-0-41-3 ∷ []) (lem-SBtgtd-at0440 c4) ▸
       at 32 1 (Sb⁻2-0-41-3 ∷ []) (lem-SBtgtd-at0440 c4) ▸
       at 34 1 (CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (sym (wl0533 (lit c4))) ▸
       at 38 1 (Sb⁻2-4-01-3 ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ []) (lem-F5d-CS01-at0440 c4) ▸
       at 38 1 (Sb⁻2-0-41-3 ∷ []) (lem-SBtgtd-at0440 c4) ▸
       at 40 1 (Sb⁻2-0-41-3 ∷ []) (lem-SBtgtd-at0440 c4) ▸
       at 42 1 (CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (sym (wl0533 (lit c4))) ▸
       at 46 1 (Sb⁻2-4-01-3 ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ []) (lem-F5d-CS01-at0440 c4) ▸ done

  b11 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ Sb⁻2-4-01-3 ∷ X0 ∷ S4 ∷ ι⁻ ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b11 = at 46 1 (Sb⁻2-0-41-3 ∷ []) (lem-SBtgtd-at0440 c4) ▸
       at 48 1 (Sb⁻2-0-41-3 ∷ []) (lem-SBtgtd-at0440 c4) ▸
       at 50 1 (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (wp0207 c4) ▸
       at 54 1 (S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ []) (sym (wl0534 (lit c4))) ▸
       at 34 1 (CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ []) (wl0535 (lit c4)) ▸
       at 32 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 33 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 36 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b12 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b12 = at 39 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 42 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 44 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 44 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 45 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 48 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 51 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 52 4 (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0536 (lit c4))) ▸ done

  b13 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b13 = at 49 4 (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0208 c4)) ▸
       at 46 4 (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0536 (lit c4))) ▸
       at 43 4 (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0208 c4)) ▸
       at 46 2 [] (wl0509 (lit c4)) ▸
       at 47 2 [] (wl0509 (lit c4)) ▸
       at 48 2 [] (wl0509 (lit c4)) ▸
       at 45 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 45 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸ done

  b14 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b14 = at 40 4 (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0209 c4)) ▸
       at 38 1 (CS03⁻ ∷ []) (refl) ▸
       at 37 4 (CS01⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0537 (lit c4))) ▸
       at 39 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 34 4 (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0209 c4)) ▸
       at 32 1 (CS03 ∷ []) (refl) ▸
       at 31 4 (CS01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0538 (lit c4))) ▸
       at 33 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b15 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b15 = at 34 2 [] (wl0509 (lit c4)) ▸
       at 35 2 [] (wl0509 (lit c4)) ▸
       at 36 2 [] (wl0509 (lit c4)) ▸
       at 37 2 [] (wl0509 (lit c4)) ▸
       at 33 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 33 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b16 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b16 = at 40 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 43 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 45 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 45 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 45 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 46 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 49 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 52 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b17 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b17 = at 55 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 54 2 (K1⁻ ∷ CCZ234 ∷ []) (sym (c₂ ((K • iI) ↑) (CCZ))) ▸
       at 53 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 55 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 56 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 59 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 62 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 65 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b18 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b18 = at 66 4 (CS01⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) (sym (wp0210 c4)) ▸
       at 63 4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (sym (wl0539 (lit c4))) ▸
       at 60 4 (CS01⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (sym (wl0540 (lit c4))) ▸
       at 57 4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (sym (wl0539 (lit c4))) ▸
       at 54 4 (CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) (sym (wl0541 (lit c4))) ▸
       at 57 2 [] (wl0509 (lit c4)) ▸
       at 58 2 [] (wl0509 (lit c4)) ▸
       at 59 2 [] (wl0509 (lit c4)) ▸ done

  b19 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ K1⁻ ∷ CCZ234 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b19 = at 60 2 [] (wl0509 (lit c4)) ▸
       at 56 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 57 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 56 2 (K1⁻ ∷ CCZ234 ∷ []) (sym (c₂ ((K • iI) ↑) (CCZ))) ▸
       at 55 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 50 6 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (sym (wl0542 (lit c4))) ▸
       at 49 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 48 2 (K1⁻ ∷ CCZ234 ∷ []) (sym (c₂ ((K • iI) ↑) (CCZ))) ▸ done

  b20 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ K1⁻ ∷ CCZ234 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b20 = at 47 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 49 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 50 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 53 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 56 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 59 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 60 4 (CS01⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) (sym (wp0210 c4)) ▸
       at 57 4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (sym (wl0539 (lit c4))) ▸ done

  b21 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ CCZ234 ∷ X0 ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b21 = at 54 4 (CS01⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (sym (wl0540 (lit c4))) ▸
       at 51 4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (sym (wl0539 (lit c4))) ▸
       at 48 4 (CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) (sym (wl0541 (lit c4))) ▸
       at 51 2 [] (wl0509 (lit c4)) ▸
       at 52 2 [] (wl0509 (lit c4)) ▸
       at 53 2 [] (wl0509 (lit c4)) ▸
       at 54 2 [] (wl0509 (lit c4)) ▸
       at 50 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸ done

  b22 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ CCZ234 ∷ X0 ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Bx2-0143 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b22 = at 51 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 50 2 (K1⁻ ∷ CCZ234 ∷ []) (sym (c₂ ((K • iI) ↑) (CCZ))) ▸
       at 49 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 44 6 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (sym (wl0542 (lit c4))) ▸
       at 49 2 [] (wl0509 (lit c4)) ▸
       at 50 2 [] (wl0509 (lit c4)) ▸
       at 51 2 [] (wl0509 (lit c4)) ▸
       at 48 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸ done

  b23 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Bx2-0143 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b23 = at 48 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 48 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 39 1 (CS03⁻ ∷ []) (refl) ▸
       at 35 12 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0211 c4)) ▸
       at 42 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 33 1 (CS03 ∷ []) (refl) ▸
       at 32 6 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0543 (lit c4))) ▸
       at 36 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b24 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b24 = at 37 2 [] (wl0509 (lit c4)) ▸
       at 38 2 [] (wl0509 (lit c4)) ▸
       at 39 2 [] (wl0509 (lit c4)) ▸
       at 40 2 [] (wl0509 (lit c4)) ▸
       at 36 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 36 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 40 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b25 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b25 = at 43 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 46 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 48 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 48 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 49 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 52 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 55 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 56 4 (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0536 (lit c4))) ▸ done

  b26 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b26 = at 53 4 (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0208 c4)) ▸
       at 50 4 (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0536 (lit c4))) ▸
       at 47 4 (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0208 c4)) ▸
       at 50 2 [] (wl0509 (lit c4)) ▸
       at 51 2 [] (wl0509 (lit c4)) ▸
       at 52 2 [] (wl0509 (lit c4)) ▸
       at 49 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 49 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸ done

  b27 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b27 = at 44 4 (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0209 c4)) ▸
       at 42 1 (CS03⁻ ∷ []) (refl) ▸
       at 41 4 (CS01⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0537 (lit c4))) ▸
       at 43 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 38 4 (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0209 c4)) ▸
       at 36 1 (CS03 ∷ []) (refl) ▸
       at 35 4 (CS01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0538 (lit c4))) ▸
       at 37 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b28 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b28 = at 38 2 [] (wl0509 (lit c4)) ▸
       at 39 2 [] (wl0509 (lit c4)) ▸
       at 40 2 [] (wl0509 (lit c4)) ▸
       at 41 2 [] (wl0509 (lit c4)) ▸
       at 37 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 37 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 41 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b29 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b29 = at 44 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 47 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 49 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 49 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 50 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 53 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 56 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 57 4 (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0510 (lit c4))) ▸ done

  b30 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b30 = at 54 4 (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0190 c4)) ▸
       at 51 4 (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0510 (lit c4))) ▸
       at 48 4 (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0190 c4)) ▸
       at 51 2 [] (wl0509 (lit c4)) ▸
       at 52 2 [] (wl0509 (lit c4)) ▸
       at 53 2 [] (wl0509 (lit c4)) ▸
       at 50 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 50 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸ done

  b31 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b31 = at 45 4 (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0191 c4)) ▸
       at 43 1 (CS03⁻ ∷ []) (refl) ▸
       at 42 4 (S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0512 (lit c4))) ▸
       at 44 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 39 4 (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0191 c4)) ▸
       at 37 1 (CS03 ∷ []) (refl) ▸
       at 36 4 (S0 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0511 (lit c4))) ▸
       at 38 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b32 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b32 = at 39 2 [] (wl0509 (lit c4)) ▸
       at 40 2 [] (wl0509 (lit c4)) ▸
       at 41 2 [] (wl0509 (lit c4)) ▸
       at 42 2 [] (wl0509 (lit c4)) ▸
       at 38 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 39 2 (ι⁻ ∷ X0 ∷ []) (zc⁻) ▸
       at 38 2 (ι⁻ ∷ Sb⁻2-0-41-3 ∷ []) (zc⁻) ▸
       at 37 2 (ι⁻ ∷ X0 ∷ []) (zc⁻) ▸ done

  b33 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b33 = at 31 7 (CK01⁻ ∷ []) (sym (wl0535 (lit c4))) ▸
       at 38 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 38 1 (CS03 ∷ []) (refl) ▸
       at 35 4 (CS03 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (sym (wl0544 (lit c4))) ▸
       at 35 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 40 1 (CS03⁻ ∷ []) (refl) ▸
       at 36 6 (Toff314 ∷ CS03⁻ ∷ Toff314 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (sym (wp0212 c4)) ▸
       at 37 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b34 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CCZ234 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b34 = at 42 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 42 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 42 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 39 4 (Toff201 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (sym (wl0545 (lit c4))) ▸
       at 42 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 41 2 (CCZ234 ∷ CK01⁻ ∷ []) (c₂ (S • CK₀₁) (CCZ)) ▸
       at 40 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 41 4 (Toff201 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (sym (wl0545 (lit c4))) ▸ done

  b35 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CCZ234 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b35 = at 44 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 43 2 (CCZ234 ∷ CK01⁻ ∷ []) (c₂ (S • CK₀₁) (CCZ)) ▸
       at 42 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 39 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 39 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 39 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 35 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 35 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸ done

  b36 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b36 = at 35 1 (CS03 ∷ []) (refl) ▸
       at 33 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 40 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 43 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 45 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 45 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸ done

  b37 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b37 = at 46 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 49 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 52 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 53 4 (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 50 4 (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0203 c4)) ▸
       at 47 4 (CS03 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 44 4 (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0203 c4)) ▸
       at 47 2 [] (wl0509 (lit c4)) ▸ done

  b38 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b38 = at 48 2 [] (wl0509 (lit c4)) ▸
       at 49 2 [] (wl0509 (lit c4)) ▸
       at 46 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 46 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 39 1 (CS03⁻ ∷ []) (refl) ▸
       at 35 10 (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0213 c4)) ▸
       at 40 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 33 1 (CS03 ∷ []) (refl) ▸ done

  b39 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b39 = at 32 4 (CS03 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0546 (lit c4))) ▸
       at 34 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 35 2 [] (wl0509 (lit c4)) ▸
       at 36 2 [] (wl0509 (lit c4)) ▸
       at 37 2 [] (wl0509 (lit c4)) ▸
       at 38 2 [] (wl0509 (lit c4)) ▸
       at 34 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 32 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b40 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CS03⁻ ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b40 = at 35 2 (Toff314 ∷ X0 ∷ []) (sym (wp0202 c4)) ▸
       at 34 2 (Toff314 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4) ▸
       at 33 2 (Toff314 ∷ X0 ∷ []) (sym (wp0202 c4)) ▸
       at 37 1 (CS03⁻ ∷ []) (refl) ▸
       at 35 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 36 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 39 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 42 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b41 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CS03⁻ ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b41 = at 45 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 47 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 47 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 48 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 51 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 54 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 55 4 (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 52 4 (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0200 c4)) ▸ done

  b42 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b42 = at 49 4 (CS03⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 46 4 (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0200 c4)) ▸
       at 49 2 [] (wl0509 (lit c4)) ▸
       at 50 2 [] (wl0509 (lit c4)) ▸
       at 51 2 [] (wl0509 (lit c4)) ▸
       at 48 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 48 1 (Bx⁻2-0413 ∷ []) (sym (lem-BOXd-BOX-at0210243143 c4)) ▸
       at 41 1 (CS03⁻ ∷ []) (refl) ▸ done

  b43 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b43 = at 37 10 (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0214 c4)) ▸
       at 42 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 35 1 (CS03 ∷ []) (refl) ▸
       at 34 4 (CS03⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 36 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 37 2 [] (wl0509 (lit c4)) ▸
       at 38 2 [] (wl0509 (lit c4)) ▸
       at 39 2 [] (wl0509 (lit c4)) ▸ done

  b44 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ X0 ∷ Bx⁻2-0413 ∷ X0 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Bx2-0431 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b44 = at 40 2 [] (wl0509 (lit c4)) ▸
       at 36 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 34 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 37 2 (Toff314 ∷ X0 ∷ []) (sym (wp0202 c4)) ▸
       at 36 2 (Toff314 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4) ▸
       at 35 2 (Toff314 ∷ X0 ∷ []) (sym (wp0202 c4)) ▸
       at 39 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 39 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸ done

  b45 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Bx2-0431 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b45 = at 39 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 39 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 37 1 (Sb⁻3-0-41-2 ∷ []) (lem-F0d c4) ▸
       at 37 1 (Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) (refl) ▸
       at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 41 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 44 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 47 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b46 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Bx⁻3-0412 ∷ X0 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Bx3-0421 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b46 = at 51 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 52 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0549 (lit c4)) ▸
       at 53 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 56 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 59 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 62 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 49 1 (Bx3-0412 ∷ []) (lem-BOXd-BOX-at0310243142 c4) ▸
       at 49 1 (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4) ▸ done

  b47 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Bx3-0421 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CS02 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b47 = at 49 1 (Bx3-0241 ∷ []) (lem-sym23-at0310243241 c4) ▸
       at 49 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at03103441 c4) ▸
       at 50 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 53 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 56 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 59 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸
       at 58 2 (K2 ∷ CCZ134 ∷ []) (wl0551 (lit c4)) ▸
       at 57 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸ done

  b48 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ X0 ∷ CCZ134 ∷ X0 ∷ CS02 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ X0 ∷ CS13 ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ CS02 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS34 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b48 = at 59 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4)) ▸
       at 60 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 63 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 66 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 69 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 70 4 (CS02 ∷ X0 ∷ CS34 ∷ X0 ∷ []) (sym (wp0215 c4)) ▸
       at 67 4 (CS02 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (sym (wp0216 c4)) ▸
       at 64 4 (CS02 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ []) (sym (wl0552 (lit c4))) ▸ done

  b49 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ X0 ∷ CS13 ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ CS02 ∷ X0 ∷ CS13⁻ ∷ X0 ∷ X0 ∷ CX41 ∷ X0 ∷ X0 ∷ CS34 ∷ X0 ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CS02 ∷ X0 ∷ CCZ134 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b49 = at 61 4 (CS02 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (sym (wp0216 c4)) ▸
       at 58 4 (CS02 ∷ X0 ∷ CS13 ∷ X0 ∷ []) (sym (wl0553 (lit c4))) ▸
       at 61 2 [] (wl0509 (lit c4)) ▸
       at 62 2 [] (wl0509 (lit c4)) ▸
       at 63 2 [] (wl0509 (lit c4)) ▸
       at 64 2 [] (wl0509 (lit c4)) ▸
       at 60 5 (CCZ134 ∷ []) (sym (wl0404 (lit c4))) ▸
       at 61 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸ done

  b50 : Chain (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ K2 ∷ CS02 ∷ X0 ∷ CCZ134 ∷ K2⁻ ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ []) (Sb2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ X0 ∷ Sb3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Sb⁻3-0-2-1 ∷ X0 ∷ X0 ∷ Toff214 ∷ X0 ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ K2 ∷ X0 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ X0 ∷ CCZ134 ∷ X0 ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS02⁻ ∷ K2⁻ ∷ K2 ∷ CX30 ∷ K2⁻ ∷ K2 ∷ CS23 ∷ K2⁻ ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ CK01⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ CS14 ∷ [])
  b50 = at 60 2 (K2⁻ ∷ CCZ134 ∷ []) (wl0554 (lit c4)) ▸
       at 59 2 (K2⁻ ∷ X0 ∷ []) (c₁ (X) ((K • iI) ↑)) ▸
       at 54 6 (K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (sym (wl0555 (lit c4))) ▸
       at 53 2 (K2 ∷ X0 ∷ []) (c₁ (X) (K ↑)) ▸ done

