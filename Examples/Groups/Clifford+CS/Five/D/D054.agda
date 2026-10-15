{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D054 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-box-perm-2431)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-box-2)
open import Examples.Groups.Clifford+CS.Five.D.D046 using (lem-CSdu-box-3-at122441 ; lem-CSu-box-3-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D047 using (lem-box-perm-1342-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D050 using (lem-CSdu-box-3-at0210243143 ; lem-CSu-box-3-at0210243143 ; lem-box-perm-1423-at021021)
open import Examples.Groups.Clifford+CS.Five.D.D053 using (lem-box-perm-4132-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX04-TOFF213 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CZ13-CCZ024 ; lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-comm-CCZ024-CX13)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-comm-CCZ034-CS12 ; lem-comm-TOFF013-CS24)
-- F4-CS2-CS0: 284 steps
lem-F4-CS2-CS0 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-CS0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (lw4 c4 (CZ02 ∷ Toff213 ∷ []) (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 6 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 7 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CZ02 ∷ []) (pw3 c4 (CZ02 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (lw3 c4 (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff213 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 2 (Bx2-0413 ∷ CS12⁻ ∷ []) (lem-CSdu-box-3-at0210243143 c4) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸ done

  b3 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b3 = at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (pw3 c4 (K1⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (pw3 c4 (K1 ∷ CCZ024 ∷ []) (CCZ024 ∷ K1 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ CCZ034 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b4 = at 5 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) (lw0 c4 (Toff134 ∷ Toff213 ∷ []) (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) (pw1 c4 (Toff234 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CCZ024 ∷ K1⁻ ∷ []) (pw3 c4 (K1⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 9 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ CCZ034 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff134 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ Toff213 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b5 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 7 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ K1 ∷ []) (pw3 c4 (K1 ∷ CCZ024 ∷ []) (CCZ024 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 7 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (Toff213 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 c4) ▸
       at 11 2 (Toff213 ∷ CS34⁻ ∷ []) (lw0 c4 (CS34⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff134 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ Toff213 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Bx2-0413 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b6 = at 10 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 c4) ▸
       at 9 2 (Toff213 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ Toff213 ∷ []) (Toff213 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 10 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff213 ∷ Toff234 ∷ []) (lw0 c4 (Toff234 ∷ Toff213 ∷ []) (Toff213 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) (lw0 c4 (Toff134 ∷ Toff213 ∷ []) (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (Toff134 ∷ []) (lw0 c4 (Toff134 ∷ Toff234 ∷ Toff234 ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸ done

  b7 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Bx2-0413 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b7 = at 3 2 (Bx2-0413 ∷ CS12 ∷ []) (lem-CSu-box-3-at0210243143 c4) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 2 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ K1⁻ ∷ []) (pw3 c4 (K1⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸ done

  b8 : Chain (X4 ∷ Bx0-2431 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ CCZ034 ∷ Toff213 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b8 = at 3 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ K1 ∷ []) (pw3 c4 (K1 ∷ CCZ024 ∷ []) (CCZ024 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 3 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) (lw0 c4 (Toff134 ∷ Toff213 ∷ []) (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) (pw1 c4 (Toff234 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (pw3 c4 (K1⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ CCZ034 ∷ Toff213 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff134 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ Toff213 ∷ CS03 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b9 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (pw3 c4 (K1 ∷ CCZ024 ∷ []) (CCZ024 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff213 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff134 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ Toff213 ∷ CS03 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b10 = at 10 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 c4) ▸
       at 9 2 (Toff213 ∷ CS34⁻ ∷ []) (lw0 c4 (CS34⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 c4) ▸
       at 7 2 (Toff213 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ Toff213 ∷ []) (Toff213 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff213 ∷ Toff234 ∷ []) (lw0 c4 (Toff234 ∷ Toff213 ∷ []) (Toff213 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) (lw0 c4 (Toff134 ∷ Toff213 ∷ []) (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (Toff134 ∷ []) (lw0 c4 (Toff134 ∷ Toff234 ∷ Toff234 ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b11 = at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-box-perm-4132-at122441 c4) ▸
       at 2 1 (Bx2-0134 ∷ []) (lem-box-perm-1342-at0210243143 c4) ▸
       at 1 2 (Bx2-0134 ∷ Bx0-1234 ∷ []) (lem-box-box-2 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-box-perm-1423-at021021 c4) ▸
       at 2 1 (Bx0-2431 ∷ []) (lem-box-perm-2431 c4) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (CCZ024 ∷ X4 ∷ CZ02 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CCZ024 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff213 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b12 = at 2 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (lw4 c4 (CZ02 ∷ Toff213 ∷ []) (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸ done

  b13 : Chain (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CCZ024 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff213 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b13 = at 5 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (pw3 c4 (CZ02 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (X4 ∷ []) (lw3 c4 (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff213 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b14 : Chain (Bx2-0413 ∷ X4 ∷ CCZ013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CZ13 ∷ CCZ013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b14 = at 2 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 3 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 3 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CZ13 ∷ CCZ013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b15 = at 5 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 6 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 6 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 c4) ▸ done

  b16 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b16 = at 5 3 (Toff013 ∷ CCZ013 ∷ []) (lw4 c4 (CZ13 ∷ CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 3 (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ013 ∷ Toff134 ∷ CCZ034 ∷ []) (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 c4) ▸
       at 5 2 (CS12 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CS12 ∷ []) (CS12 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS12⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (Bx2-0413 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ Sb0-2-43-1 ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b17 = at 10 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 c4) ▸
       at 5 2 (Toff134 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 6 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 2 (CX13 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b18 : Chain (Bx2-0413 ∷ X4 ∷ Sb0-2-43-1 ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CX13 ∷ Toff014 ∷ Toff314 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b18 = at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸
       at 6 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 6 (CX13 ∷ Toff314 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX13 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CX10 ∷ CX13 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX13 ∷ []) (CX10 ∷ CX13 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ Toff314 ∷ []) (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b19 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CX13 ∷ Toff014 ∷ Toff314 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b19 = at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 7 2 (Toff014 ∷ CCZ124 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K3 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 12 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸ done

  b20 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b20 = at 14 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K3⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 9 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX10 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX10 ∷ []) (CX10 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 c4) ▸
       at 5 2 (CX12 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX12 ∷ []) (CX12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 c4) ▸ done

  b21 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ CX13 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ Toff013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b21 = at 7 2 (CX12 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX12 ∷ []) (CX12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS14 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ CS14 ∷ []) (CS14 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 4 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX10 ∷ CX13 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX13 ∷ []) (CX10 ∷ CX13 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff014 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ Toff014 ∷ []) (Toff014 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 c4) ▸
       at 9 2 (CX12 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX12 ∷ []) (CX12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b22 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ CX13 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ Toff013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX13 ∷ Toff314 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b22 = at 10 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 c4) ▸
       at 11 2 (CX12 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX12 ∷ []) (CX12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CS14 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ CS14 ∷ []) (CS14 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 8 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ Toff314 ∷ []) (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CCZ124 ∷ []) (pw3 c4 (CX10 ∷ CCZ124 ∷ CX10 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ124 ∷ []) (pw3 c4 (Toff014 ∷ CCZ124 ∷ Toff014 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (CX13 ∷ Toff314 ∷ []) (lw0 c4 (CCZ124 ∷ CX13 ∷ CCZ124 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b23 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX13 ∷ Toff314 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CX13 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b23 = at 2 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 4 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K3 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 6 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 8 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b24 : Chain (Bx2-0413 ∷ X4 ∷ CX13 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ Sb0-2-43-1 ∷ CS03 ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b24 = at 9 2 (K3⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b25 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ Sb0-2-43-1 ∷ CS03 ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b25 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 7 2 (CS03 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CS03 ∷ []) (CS03 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS03 ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ CS03 ∷ []) (CS03 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS03 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CS03 ∷ []) (CS03 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS03 ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ CS03 ∷ []) (CS03 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS03 ∷ Bx0-2431 ∷ []) (sym (lem-CSu-box-3-at122441 c4)) ▸ done

  b26 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ [])
  b26 = at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 2 2 (CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX13 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (CS12 ∷ []) (refl) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b27 = at 5 6 (CX13 ∷ Toff314 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX13 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (CX10 ∷ CX13 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX13 ∷ []) (CX10 ∷ CX13 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ Toff314 ∷ []) (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 9 2 (Toff014 ∷ CCZ124 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b28 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 14 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 16 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K3⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 11 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b29 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ Toff013 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b29 = at 5 2 (CX10 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX10 ∷ []) (CX10 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 c4) ▸
       at 7 2 (CX12 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX12 ∷ []) (CX12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 c4) ▸
       at 9 2 (CX12 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX12 ∷ []) (CX12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CS14 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ CS14 ∷ []) (CS14 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b30 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ Toff013 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ CX13 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b30 = at 7 2 (CX10 ∷ CX13 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX13 ∷ []) (CX10 ∷ CX13 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff014 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ Toff014 ∷ []) (Toff014 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 c4) ▸
       at 11 2 (CX12 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX12 ∷ []) (CX12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 c4) ▸
       at 13 2 (CX12 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX12 ∷ []) (CX12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CS14 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ CS14 ∷ []) (CS14 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b31 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ CX13 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b31 = at 10 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ Toff314 ∷ []) (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ124 ∷ []) (pw3 c4 (CX10 ∷ CCZ124 ∷ CX10 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CCZ124 ∷ []) (pw3 c4 (Toff014 ∷ CCZ124 ∷ Toff014 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CX13 ∷ Toff314 ∷ []) (lw0 c4 (CCZ124 ∷ CX13 ∷ CCZ124 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b32 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ Toff314 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b32 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b33 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ Toff314 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS03⁻ ∷ X4 ∷ [])
  b33 = at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 3 (Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX13 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS03⁻ ∷ X4 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b34 = at 9 2 (CS03⁻ ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS03⁻ ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS03⁻ ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS03⁻ ∷ Toff134 ∷ []) (pw2 c4 (Toff134 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS03⁻ ∷ Bx0-2431 ∷ []) (sym (lem-CSdu-box-3-at122441 c4)) ▸
       at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

  b35 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b35 = at 4 2 (CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

