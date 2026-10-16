{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D113 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0393 ; wl0509 ; wl0510 ; wl0511 ; wl0512 ; wl0535 ; wl0536 ; wl0537 ; wl0538 ; wl0539 ; wl0540 ; wl0541 ; wl0542 ; wl0587 ; wl0588 ; wp0190 ; wp0191 ; wp0208 ; wp0209 ; wp0210 ; wp0251)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210213443)
-- F1 CS-K1 [rhs shape] part22: 366 steps
lem-F1-CS-K1-rhs-shape-part22 : Ws → ⟪ (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-rhs-shape-part22 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (run b45)))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b0 = at 31 2 [] (wl0509 (lit c4)) ▸
       at 32 2 [] (wl0509 (lit c4)) ▸
       at 33 2 [] (wl0509 (lit c4)) ▸
       at 34 2 [] (wl0509 (lit c4)) ▸
       at 30 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 30 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b1 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b1 = at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 40 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 42 1 (CS03⁻ ∷ []) (refl) ▸
       at 41 6 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0587 (lit c4))) ▸
       at 45 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 36 1 (CS03 ∷ []) (refl) ▸
       at 32 12 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0251 c4)) ▸
       at 39 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CCZ234 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b2 = at 30 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 30 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 40 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 39 2 (K1⁻ ∷ CCZ234 ∷ []) (sym (c₂ ((K • iI) ↑) (CCZ))) ▸
       at 38 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸ done

  b3 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CCZ234 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b3 = at 40 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 41 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 44 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 47 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 50 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 51 4 (CS01⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) (sym (wp0210 c4)) ▸
       at 48 4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (sym (wl0539 (lit c4))) ▸
       at 45 4 (CS01⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (sym (wl0540 (lit c4))) ▸ done

  b4 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ CCZ234 ∷ K1⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b4 = at 42 4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (sym (wl0539 (lit c4))) ▸
       at 39 4 (CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) (sym (wl0541 (lit c4))) ▸
       at 42 2 [] (wl0509 (lit c4)) ▸
       at 43 2 [] (wl0509 (lit c4)) ▸
       at 44 2 [] (wl0509 (lit c4)) ▸
       at 45 2 [] (wl0509 (lit c4)) ▸
       at 41 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 42 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸ done

  b5 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ CCZ234 ∷ K1⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b5 = at 41 2 (K1⁻ ∷ CCZ234 ∷ []) (sym (c₂ ((K • iI) ↑) (CCZ))) ▸
       at 40 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 35 6 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (sym (wl0542 (lit c4))) ▸
       at 34 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 33 2 (K1⁻ ∷ CCZ234 ∷ []) (sym (c₂ ((K • iI) ↑) (CCZ))) ▸
       at 32 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 34 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b6 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b6 = at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 41 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 44 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 45 4 (CS01⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) (sym (wp0210 c4)) ▸
       at 42 4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (sym (wl0539 (lit c4))) ▸
       at 39 4 (CS01⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (sym (wl0540 (lit c4))) ▸
       at 36 4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (sym (wl0539 (lit c4))) ▸
       at 33 4 (CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) (sym (wl0541 (lit c4))) ▸ done

  b7 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b7 = at 36 2 [] (wl0509 (lit c4)) ▸
       at 37 2 [] (wl0509 (lit c4)) ▸
       at 38 2 [] (wl0509 (lit c4)) ▸
       at 39 2 [] (wl0509 (lit c4)) ▸
       at 35 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 36 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 35 2 (K1⁻ ∷ CCZ234 ∷ []) (sym (c₂ ((K • iI) ↑) (CCZ))) ▸
       at 34 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸ done

  b8 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b8 = at 29 6 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (sym (wl0542 (lit c4))) ▸
       at 34 2 [] (wl0509 (lit c4)) ▸
       at 35 2 [] (wl0509 (lit c4)) ▸
       at 36 2 [] (wl0509 (lit c4)) ▸
       at 33 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 33 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 34 2 [] (wl0509 (lit c4)) ▸
       at 35 2 [] (wl0509 (lit c4)) ▸ done

  b9 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b9 = at 36 2 [] (wl0509 (lit c4)) ▸
       at 37 2 [] (wl0509 (lit c4)) ▸
       at 33 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 33 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 40 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 43 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b10 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b10 = at 45 1 (CS03⁻ ∷ []) (refl) ▸
       at 44 4 (CS01⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0537 (lit c4))) ▸
       at 46 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 41 4 (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0209 c4)) ▸
       at 39 1 (CS03 ∷ []) (refl) ▸
       at 38 4 (CS01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0538 (lit c4))) ▸
       at 40 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 35 4 (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0209 c4)) ▸ done

  b11 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b11 = at 33 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 40 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 41 4 (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0536 (lit c4))) ▸
       at 38 4 (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0208 c4)) ▸
       at 35 4 (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0536 (lit c4))) ▸
       at 32 4 (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0208 c4)) ▸ done

  b12 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b12 = at 35 2 [] (wl0509 (lit c4)) ▸
       at 36 2 [] (wl0509 (lit c4)) ▸
       at 37 2 [] (wl0509 (lit c4)) ▸
       at 34 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 35 2 [] (wl0509 (lit c4)) ▸
       at 36 2 [] (wl0509 (lit c4)) ▸
       at 37 2 [] (wl0509 (lit c4)) ▸
       at 38 2 [] (wl0509 (lit c4)) ▸ done

  b13 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b13 = at 34 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 34 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 41 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 44 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 46 1 (CS03⁻ ∷ []) (refl) ▸
       at 45 4 (S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0512 (lit c4))) ▸ done

  b14 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b14 = at 47 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 42 4 (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0191 c4)) ▸
       at 40 1 (CS03 ∷ []) (refl) ▸
       at 39 4 (S0 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0511 (lit c4))) ▸
       at 41 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 36 4 (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0191 c4)) ▸
       at 34 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b15 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b15 = at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 41 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 42 4 (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0510 (lit c4))) ▸
       at 39 4 (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0190 c4)) ▸
       at 36 4 (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0510 (lit c4))) ▸
       at 33 4 (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0190 c4)) ▸
       at 36 2 [] (wl0509 (lit c4)) ▸
       at 37 2 [] (wl0509 (lit c4)) ▸ done

  b16 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ X0 ∷ Sb2-0-41-3 ∷ ι⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b16 = at 38 2 [] (wl0509 (lit c4)) ▸
       at 35 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 36 2 [] (wl0509 (lit c4)) ▸
       at 37 2 [] (wl0509 (lit c4)) ▸
       at 38 2 [] (wl0509 (lit c4)) ▸
       at 39 2 [] (wl0509 (lit c4)) ▸
       at 35 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 36 2 (ι⁻ ∷ X0 ∷ []) (zc⁻) ▸ done

  b17 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ X0 ∷ Sb2-0-41-3 ∷ ι⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b17 = at 35 2 (ι⁻ ∷ Sb2-0-41-3 ∷ []) (zc⁻) ▸
       at 34 2 (ι⁻ ∷ X0 ∷ []) (zc⁻) ▸
       at 28 7 (CK01⁻ ∷ []) (sym (wl0535 (lit c4))) ▸
       at 25 4 (CK01⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl0588 (lit c4))) ▸
       at 25 1 (CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ []) (wl0535 (lit c4)) ▸
       at 23 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 24 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 27 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b18 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b18 = at 30 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 33 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 1 (CS03⁻ ∷ []) (refl) ▸
       at 34 4 (CS01⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0537 (lit c4))) ▸
       at 36 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 31 4 (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0209 c4)) ▸
       at 29 1 (CS03 ∷ []) (refl) ▸
       at 28 4 (CS01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0538 (lit c4))) ▸ done

  b19 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b19 = at 30 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 25 4 (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0209 c4)) ▸
       at 23 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 24 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 27 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 30 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 4 (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0536 (lit c4))) ▸
       at 28 4 (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0208 c4)) ▸ done

  b20 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b20 = at 25 4 (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0536 (lit c4))) ▸
       at 22 4 (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0208 c4)) ▸
       at 25 2 [] (wl0509 (lit c4)) ▸
       at 26 2 [] (wl0509 (lit c4)) ▸
       at 27 2 [] (wl0509 (lit c4)) ▸
       at 24 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 25 2 [] (wl0509 (lit c4)) ▸
       at 26 2 [] (wl0509 (lit c4)) ▸ done

  b21 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b21 = at 27 2 [] (wl0509 (lit c4)) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 24 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 24 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 25 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b22 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b22 = at 36 1 (CS03⁻ ∷ []) (refl) ▸
       at 35 6 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0587 (lit c4))) ▸
       at 39 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 30 1 (CS03 ∷ []) (refl) ▸
       at 26 12 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0251 c4)) ▸
       at 33 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 24 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 24 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸ done

  b23 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b23 = at 25 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 33 2 (K1⁻ ∷ CCZ234 ∷ []) (sym (c₂ ((K • iI) ↑) (CCZ))) ▸
       at 32 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 34 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b24 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b24 = at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 41 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 44 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 45 4 (CS01⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) (sym (wp0210 c4)) ▸
       at 42 4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (sym (wl0539 (lit c4))) ▸
       at 39 4 (CS01⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (sym (wl0540 (lit c4))) ▸
       at 36 4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (sym (wl0539 (lit c4))) ▸
       at 33 4 (CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) (sym (wl0541 (lit c4))) ▸ done

  b25 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b25 = at 36 2 [] (wl0509 (lit c4)) ▸
       at 37 2 [] (wl0509 (lit c4)) ▸
       at 38 2 [] (wl0509 (lit c4)) ▸
       at 39 2 [] (wl0509 (lit c4)) ▸
       at 35 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 36 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 35 2 (K1⁻ ∷ CCZ234 ∷ []) (sym (c₂ ((K • iI) ↑) (CCZ))) ▸
       at 34 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸ done

  b26 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ CS24 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b26 = at 29 6 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (sym (wl0542 (lit c4))) ▸
       at 28 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 27 2 (K1⁻ ∷ CCZ234 ∷ []) (sym (c₂ ((K • iI) ↑) (CCZ))) ▸
       at 26 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 28 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b27 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ CS24 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b27 = at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 39 4 (CS01⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) (sym (wp0210 c4)) ▸
       at 36 4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (sym (wl0539 (lit c4))) ▸
       at 33 4 (CS01⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (sym (wl0540 (lit c4))) ▸
       at 30 4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (sym (wl0539 (lit c4))) ▸
       at 27 4 (CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) (sym (wl0541 (lit c4))) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸ done

  b28 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b28 = at 32 2 [] (wl0509 (lit c4)) ▸
       at 33 2 [] (wl0509 (lit c4)) ▸
       at 29 5 (CCZ234 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 30 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 29 2 (K1⁻ ∷ CCZ234 ∷ []) (sym (c₂ ((K • iI) ↑) (CCZ))) ▸
       at 28 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 23 6 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (sym (wl0542 (lit c4))) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸ done

  b29 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b29 = at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 27 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 27 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 28 2 [] (wl0509 (lit c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸ done

  b30 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b30 = at 27 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 27 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 37 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 39 1 (CS03⁻ ∷ []) (refl) ▸
       at 38 4 (CS01⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0537 (lit c4))) ▸ done

  b31 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b31 = at 40 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 35 4 (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0209 c4)) ▸
       at 33 1 (CS03 ∷ []) (refl) ▸
       at 32 4 (CS01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0538 (lit c4))) ▸
       at 34 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 29 4 (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0209 c4)) ▸
       at 27 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b32 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b32 = at 31 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 34 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 4 (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0536 (lit c4))) ▸
       at 32 4 (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0208 c4)) ▸
       at 29 4 (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0536 (lit c4))) ▸
       at 26 4 (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0208 c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸ done

  b33 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b33 = at 31 2 [] (wl0509 (lit c4)) ▸
       at 28 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 29 2 [] (wl0509 (lit c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸
       at 32 2 [] (wl0509 (lit c4)) ▸
       at 28 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 28 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b34 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b34 = at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 40 1 (CS03⁻ ∷ []) (refl) ▸
       at 39 4 (S0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0512 (lit c4))) ▸
       at 41 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 36 4 (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0191 c4)) ▸ done

  b35 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b35 = at 34 1 (CS03 ∷ []) (refl) ▸
       at 33 4 (S0 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0511 (lit c4))) ▸
       at 35 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 30 4 (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0191 c4)) ▸
       at 28 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b36 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b36 = at 36 4 (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0510 (lit c4))) ▸
       at 33 4 (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0190 c4)) ▸
       at 30 4 (S0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0510 (lit c4))) ▸
       at 27 4 (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0190 c4)) ▸
       at 30 2 [] (wl0509 (lit c4)) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸
       at 32 2 [] (wl0509 (lit c4)) ▸
       at 29 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸ done

  b37 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b37 = at 30 2 [] (wl0509 (lit c4)) ▸
       at 31 2 [] (wl0509 (lit c4)) ▸
       at 32 2 [] (wl0509 (lit c4)) ▸
       at 33 2 [] (wl0509 (lit c4)) ▸
       at 29 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 30 2 (ι⁻ ∷ X0 ∷ []) (zc⁻) ▸
       at 29 2 (ι⁻ ∷ Sb2-0-41-3 ∷ []) (zc⁻) ▸
       at 28 2 (ι⁻ ∷ X0 ∷ []) (zc⁻) ▸ done

  b38 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b38 = at 22 7 (CK01⁻ ∷ []) (sym (wl0535 (lit c4))) ▸
       at 19 4 (CK01⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl0588 (lit c4))) ▸
       at 19 1 (CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ []) (wl0535 (lit c4)) ▸
       at 17 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 18 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 21 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 24 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 27 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b39 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b39 = at 29 1 (CS03⁻ ∷ []) (refl) ▸
       at 28 4 (CS01⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0537 (lit c4))) ▸
       at 30 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 25 4 (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0209 c4)) ▸
       at 23 1 (CS03 ∷ []) (refl) ▸
       at 22 4 (CS01⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (sym (wl0538 (lit c4))) ▸
       at 24 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 19 4 (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0209 c4)) ▸ done

  b40 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b40 = at 17 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 18 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 21 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 24 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 25 4 (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0536 (lit c4))) ▸
       at 22 4 (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0208 c4)) ▸
       at 19 4 (CS01⁻ ∷ X0 ∷ CCZ123 ∷ X0 ∷ []) (sym (wl0536 (lit c4))) ▸
       at 16 4 (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (sym (wp0208 c4)) ▸ done

  b41 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff204 ∷ X0 ∷ X0 ∷ CCZ123 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b41 = at 19 2 [] (wl0509 (lit c4)) ▸
       at 20 2 [] (wl0509 (lit c4)) ▸
       at 21 2 [] (wl0509 (lit c4)) ▸
       at 18 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 19 2 [] (wl0509 (lit c4)) ▸
       at 20 2 [] (wl0509 (lit c4)) ▸
       at 21 2 [] (wl0509 (lit c4)) ▸
       at 22 2 [] (wl0509 (lit c4)) ▸ done

  b42 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b42 = at 18 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 18 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 19 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 22 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 25 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 28 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 30 1 (CS03⁻ ∷ []) (refl) ▸
       at 29 6 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (sym (wl0587 (lit c4))) ▸ done

  b43 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Bx2-0413 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b43 = at 33 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 24 1 (CS03 ∷ []) (refl) ▸
       at 20 12 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (sym (wp0251 c4)) ▸
       at 27 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 18 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 18 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 19 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 22 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b44 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ CS24 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b44 = at 25 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 28 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 27 2 (K1⁻ ∷ CCZ234 ∷ []) (sym (c₂ ((K • iI) ↑) (CCZ))) ▸
       at 26 2 (K1⁻ ∷ X0 ∷ []) (c₁ (X) (K • iI)) ▸
       at 28 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4)) ▸
       at 29 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 32 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 35 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸ done

  b45 : Chain (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ CS24 ∷ X0 ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ CK01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ CS01⁻ ∷ X0 ∷ Toff201 ∷ X0 ∷ X0 ∷ CCZ234 ∷ X0 ∷ X0 ∷ Toff201 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ X0 ∷ CX43 ∷ X0 ∷ X0 ∷ CS24 ∷ X0 ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb2-0-3-1 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ Sb⁻2-0-3-1 ∷ X0 ∷ CS01⁻ ∷ S0 ∷ ι⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-0-41-3 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ CK01⁻ ∷ Sb⁻2-0-41-3 ∷ CS04 ∷ S0⁻ ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ X0 ∷ Sb⁻2-0-41-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0⁻ ∷ X0 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b45 = at 38 0 (X0 ∷ X0 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 39 4 (CS01⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) (sym (wp0210 c4)) ▸
       at 36 4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (sym (wl0539 (lit c4))) ▸
       at 33 4 (CS01⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (sym (wl0540 (lit c4))) ▸
       at 30 4 (CS01⁻ ∷ X0 ∷ CX43 ∷ X0 ∷ []) (sym (wl0539 (lit c4))) ▸
       at 27 4 (CS01⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) (sym (wl0541 (lit c4))) ▸ done

