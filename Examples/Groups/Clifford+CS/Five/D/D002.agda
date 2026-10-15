{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D002 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-Xb-box-at0210243143 ; lem-box-cP-at0210243143 ; lem-box-tQ-at0210243143 ; lem-tP-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX04-TOFF213 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX14-CCZ023 ; lem-comm-CX23-CCZ014 ; lem-comm-CZ04-TOFF213 ; lem-comm-TOFF014-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CSd24-TOFF013 ; lem-comm-CX14-TOFF023 ; lem-comm-CX24-CCZ013 ; lem-comm-CZ14-CCZ023 ; lem-comm-CZ14-TOFF023 ; lem-comm-TOFF024-CSd13)
-- t-cP @0210243143: 5 steps
lem-t-cP-at0210243143 : Complete 4 → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-t-cP-at0210243143 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ [])
  b0 = at 0 2 (CCZ024 ∷ Toff204 ∷ CZ04 ∷ []) (pw1 c4 (Toff204 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff204 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 c4) ▸
       at 1 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0210243143 c4) ▸
       at 2 3 (CCZ024 ∷ Toff204 ∷ []) (pw1 c4 (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0210243143 c4) ▸ done


-- box2 @0210243143: 11 steps
lem-box2-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0413 ∷ Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  b0 = at 0 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 0 (Toff204 ∷ Toff204 ∷ []) (pw1 c4 [] (Toff204 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) (lem-t-cP-at0210243143 c4) ▸
       at 5 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 4 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) []
  b1 = at 2 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5-01: 112 steps
lem-F5-01 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-F5-01 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 2 (X4 ∷ Sb⁻2-0-3-1 ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (X)) ▸
       at 4 2 (X4 ∷ CX13 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (X4 ∷ Sb2-0-3-1 ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) (X)) ▸
       at 4 1 (CS03 ∷ []) (refl) ▸
       at 4 2 (CX13 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ []) (CX13 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 2 2 (X4 ∷ CX13 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX13 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ CX13 ∷ []) (CX13 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS01 ∷ Toff314 ∷ []) (pw2 c4 (Toff314 ∷ CS01 ∷ []) (CS01 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ []) (pw2 c4 (Toff314 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 2 6 (X4 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) (pw2 c4 (X4 ∷ CX13 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) (X4 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-Xb-box-at0210243143 c4) ▸
       at 9 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 8 1 (CS03⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b2 = at 8 2 (CCZ024 ∷ CS03⁻ ∷ []) (pw1 c4 (CS03⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CCZ024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 10 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b3 = at 7 2 (CCZ024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ CCZ024 ∷ []) (CCZ024 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 8 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS03 ∷ []) (refl) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸ done

  b4 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CCZ024 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ CCZ024 ∷ []) (CCZ024 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CCZ024 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CCZ024 ∷ CS03 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b5 = at 6 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 4 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 4 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (Bx2-0413 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CCZ024 ∷ CS03 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b6 = at 4 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 2 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 6 (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff213 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff213 ∷ []) (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS01 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b7 = at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff213 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 c4) ▸
       at 7 2 (Toff213 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 c4) ▸
       at 5 2 (Toff213 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff213 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS01 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b8 = at 3 2 (Toff213 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff213 ∷ []) (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ024 ∷ CS03⁻ ∷ []) (pw1 c4 (CS03⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 15 2 (CCZ024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 12 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CCZ024 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b9 = at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 10 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ CCZ024 ∷ []) (CCZ024 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 10 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (pw3 c4 (Toff214 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CCZ024 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b10 = at 4 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ CCZ024 ∷ []) (CCZ024 ∷ K3 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff213 ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b11 = at 5 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (pw3 c4 (Toff214 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (Toff314 ∷ CS01 ∷ CS03 ∷ []) (pw2 c4 (CCZ014 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) (Toff314 ∷ CS01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff213 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff213 ∷ []) (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (Toff213 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 c4) ▸ done

  b12 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff213 ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b12 = at 11 2 (Toff213 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 c4) ▸
       at 9 2 (Toff213 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 10 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff213 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ Toff213 ∷ []) (Toff213 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff213 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff213 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff213 ∷ []) (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (CS01 ∷ [])
  b13 = at 4 2 (Toff213 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ Toff213 ∷ []) (Toff213 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff314 ∷ []) (lw0 c4 (Toff214 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CCZ014 ∷ []) (pw3 c4 (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 0 2 [] (lem-box2-at0210243143 c4) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 10 (CS01 ∷ []) (pw2 c4 (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸ done


-- cQ @243243: 7 steps
lem-cQ-at243243 : Complete 4 → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 c4) ▸
       at 2 2 (CCZ023 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 c4) ▸
       at 0 2 (CCZ023 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ014 ∷ []) (pw2 c4 (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- tP @243243: 7 steps
lem-tP-at243243 : Complete 4 → ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-tP-at243243 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (pw2 c4 (Toff014 ∷ []) (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (lw4 c4 (Toff023 ∷ []) (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at243243 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff023 ∷ []) (lw4 c4 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff014 ∷ []) (pw2 c4 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (Toff014 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @243243: 14 steps
lem-VPQ-at243243 : Complete 4 → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (pw2 c4 (Toff014 ∷ CCZ014 ∷ []) (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (lw4 c4 (Toff023 ∷ CCZ023 ∷ []) (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑)) ▸
       at 2 2 (CS23⁻ ∷ Toff014 ∷ []) (lem-comm-TOFF014-CSd23 c4) ▸
       at 1 2 (CS23⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑)) ▸
       at 0 2 (CS23⁻ ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at243243 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS14⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 c4) ▸
       at 3 2 (S0⁻ ∷ CS14⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff023 ∷ CCZ023 ∷ []) (lw4 c4 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff014 ∷ CCZ014 ∷ []) (pw2 c4 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @243243: 3 steps
lem-QVQ-at243243 : Complete 4 → ⟪ (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-QVQ-at243243 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ [])
  b0 = at 0 0 (Toff023 ∷ Toff023 ∷ []) (lw4 c4 [] (Toff023 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at243243 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @243243: 12 steps
lem-box-cP-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-box-cP-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1423 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (lw4 c4 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (lw4 c4 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-QVQ-at243243 c4) ▸
       at 1 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at243243 c4) ▸
       at 2 2 [] (pw2 c4 (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl) ▸ done


-- Xb-box @243243: 18 steps
lem-Xb-box-at243243 : Complete 4 → ⟪ (X4 ∷ Bx0-1423 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CCZ014 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (pw2 c4 (X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (lw4 c4 (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CCZ014 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ X4 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CZ01 ∷ []) (pw2 c4 (CZ01 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (pw2 c4 (X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (X4 ∷ []) (lw2 c4 (X4 ∷ CZ01 ∷ CZ01 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b2 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @243243: 13 steps
lem-box-tQ-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1423 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (lw4 c4 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (lw4 c4 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) (pw2 c4 (CCZ014 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 c4) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at243243 c4) ▸
       at 2 4 (Toff014 ∷ []) (pw2 c4 (CCZ014 ∷ CZ14 ∷ Toff014 ∷ CCZ014 ∷ []) (Toff014 ∷ []) tt tt Eq.refl) ▸ done


-- t-cP @243243: 5 steps
lem-t-cP-at243243 : Complete 4 → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-t-cP-at243243 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ [])
  b0 = at 0 2 (CCZ014 ∷ Toff014 ∷ CZ14 ∷ []) (pw2 c4 (Toff014 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff014 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF023 c4) ▸
       at 1 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at243243 c4) ▸
       at 2 3 (CCZ014 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at243243 c4) ▸ done


-- box2 @243243: 11 steps
lem-box2-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1423 ∷ Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  b0 = at 0 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 0 (Toff014 ∷ Toff014 ∷ []) (pw2 c4 [] (Toff014 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ []) (lem-t-cP-at243243 c4) ▸
       at 5 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 4 2 [] (pw2 c4 (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) []
  b1 = at 2 2 [] (pw2 c4 (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 [] (pw2 c4 (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5-12: 112 steps
lem-F5-12 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-F5-12 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ X4 ∷ CX23 ∷ CS12 ∷ CCZ123 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 2 (X4 ∷ Sb⁻0-1-3-2 ∷ []) (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (X)) ▸
       at 4 2 (X4 ∷ CX23 ∷ Toff324 ∷ []) (lw0 c4 (Toff324 ∷ X4 ∷ []) (X4 ∷ CX23 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (X4 ∷ Sb0-1-3-2 ∷ []) (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X)) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸
       at 4 2 (CX23 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ X4 ∷ CX23 ∷ CS12 ∷ CCZ123 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 2 2 (X4 ∷ CX23 ∷ Toff324 ∷ []) (lw0 c4 (Toff324 ∷ X4 ∷ []) (X4 ∷ CX23 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX23 ∷ Toff324 ∷ []) (lw0 c4 (Toff324 ∷ CX23 ∷ []) (CX23 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS12 ∷ Toff324 ∷ []) (lw0 c4 (Toff324 ∷ CS12 ∷ []) (CS12 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ []) (lw0 c4 (Toff324 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 2 6 (X4 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ CX23 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ []) (X4 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-Xb-box-at243243 c4) ▸
       at 9 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 8 1 (CS13⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b2 = at 8 2 (CCZ014 ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CCZ014 ∷ K3⁻ ∷ []) (pw2 c4 (K3⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CCZ014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 10 2 (CCZ014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 8 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b3 = at 7 2 (CCZ014 ∷ K3 ∷ []) (pw2 c4 (K3 ∷ CCZ014 ∷ []) (CCZ014 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 8 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ014 ∷ K3⁻ ∷ []) (pw2 c4 (K3⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸ done

  b4 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b4 = at 8 2 (CCZ014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 6 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ K3 ∷ []) (pw2 c4 (K3 ∷ CCZ014 ∷ []) (CCZ014 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b5 = at 6 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 4 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 4 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (Bx0-1423 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b6 = at 4 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 2 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 2 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 6 (Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff023 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ Toff023 ∷ []) (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS12 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b7 = at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 7 2 (Toff023 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 5 2 (Toff023 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS12 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b8 = at 3 2 (Toff023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ Toff023 ∷ []) (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ014 ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 15 2 (CCZ014 ∷ K3⁻ ∷ []) (pw2 c4 (K3⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 12 2 (CCZ014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CCZ014 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b9 = at 11 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 10 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ K3 ∷ []) (pw2 c4 (K3 ∷ CCZ014 ∷ []) (CCZ014 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 10 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (pw3 c4 (Toff024 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS12 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CCZ014 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b10 = at 4 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ014 ∷ K3⁻ ∷ []) (pw2 c4 (K3⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 7 2 (CCZ014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 5 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ K3 ∷ []) (pw2 c4 (K3 ∷ CCZ014 ∷ []) (CCZ014 ∷ K3 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff023 ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b11 = at 5 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (pw3 c4 (Toff024 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (Toff324 ∷ CS12 ∷ CS13 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ []) (Toff324 ∷ CS12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff023 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ Toff023 ∷ []) (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (Toff023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸ done

  b12 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff023 ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b12 = at 11 2 (Toff023 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 9 2 (Toff023 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 10 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff023 ∷ Toff024 ∷ []) (pw1 c4 (Toff024 ∷ Toff023 ∷ []) (Toff023 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ Toff023 ∷ []) (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (CS12 ∷ [])
  b13 = at 4 2 (Toff023 ∷ Toff024 ∷ []) (pw1 c4 (Toff024 ∷ Toff023 ∷ []) (Toff023 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff324 ∷ []) (pw1 c4 (Toff024 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CCZ124 ∷ []) (pw3 c4 (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 0 2 [] (lem-box2-at243243 c4) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 10 (CS12 ∷ []) (lw0 c4 (Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS12 ∷ []) tt tt Eq.refl) ▸ done


-- cQ @122441: 7 steps
lem-cQ-at122441 : Complete 4 → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at122441 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 c4) ▸
       at 2 2 (CCZ013 ∷ CS04⁻ ∷ []) (pw2 c4 (CS04⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 c4) ▸
       at 0 2 (CCZ013 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ024 ∷ []) (pw1 c4 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸ done


-- tP @122441: 7 steps
lem-tP-at122441 : Complete 4 → ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-tP-at122441 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (pw1 c4 (Toff024 ∷ []) (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at122441 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff024 ∷ []) (pw1 c4 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (Toff024 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @122441: 14 steps
lem-VPQ-at122441 : Complete 4 → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at122441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (pw1 c4 (Toff024 ∷ CCZ024 ∷ []) (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (lw4 c4 (Toff013 ∷ CCZ013 ∷ []) (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS13⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 2 2 (CS13⁻ ∷ Toff024 ∷ []) (lem-comm-TOFF024-CSd13 c4) ▸
       at 1 2 (CS13⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 2 (CS13⁻ ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at122441 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS24⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 c4) ▸
       at 3 2 (S0⁻ ∷ CS24⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff013 ∷ CCZ013 ∷ []) (lw4 c4 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff024 ∷ CCZ024 ∷ []) (pw1 c4 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

