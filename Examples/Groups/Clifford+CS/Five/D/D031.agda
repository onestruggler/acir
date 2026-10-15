{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D031 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-tQ-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-cQ-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D029 using (lem-sym-ab-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D030 using (lem-cQ-at0210233441 ; lem-pairs-at0214213043 ; lem-sym-bc-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CX24-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CSd13-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-CSd23-TOFF014 ; lem-comm-TOFF023-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-comm-CS13-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-comm-CK41-CCZ023 ; lem-comm-CK41-TOFF023 ; lem-comm-CSd03-TOFF214 ; lem-comm-TOFF203-CSd14)
-- box-perm-1423 @0210243143: 3 steps
lem-box-perm-1423-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-box-perm-1423-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4) ▸
       at 0 1 (Bx2-4103 ∷ []) (lem-sym-bc-at0214203143 c4) ▸
       at 0 1 (Bx2-0341 ∷ []) (lem-pairs-at0214213043 c4) ▸ done


-- tP @0210233441: 7 steps
lem-tP-at0210233441 : Complete 4 → ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ
lem-tP-at0210233441 c4 = run b0
  where
  b0 : Chain (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (lw4 c4 (Toff203 ∷ []) (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-cQ-at0210233441 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff203 ∷ []) (lw4 c4 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @0210233441: 14 steps
lem-VPQ-at0210233441 : Complete 4 → ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at0210233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (lw4 c4 (Toff203 ∷ CCZ023 ∷ []) (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (lw0 c4 (Toff214 ∷ CCZ124 ∷ []) (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS14⁻ ∷ S2⁻ ∷ []) (lw0 c4 (S2⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS14⁻ ∷ Toff203 ∷ []) (lem-comm-TOFF203-CSd14 c4) ▸
       at 1 2 (CS14⁻ ∷ S2 ∷ []) (lw0 c4 (S2 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS14⁻ ∷ CS03⁻ ∷ []) (pw2 c4 (CS03⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S2⁻ ∷ S2 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0210233441 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (lw4 c4 [] (S2⁻ ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S2 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ S2 ∷ []) (S2 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 c4) ▸
       at 3 2 (S2⁻ ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Toff214 ∷ CCZ124 ∷ []) (lw0 c4 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff203 ∷ CCZ023 ∷ []) (lw4 c4 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff203 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @0210233441: 3 steps
lem-QVQ-at0210233441 : Complete 4 → ⟪ (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-QVQ-at0210233441 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ [])
  b0 = at 0 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at0210233441 c4)) ▸
       at 4 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @0210233441: 12 steps
lem-box-cP-at0210233441 : Complete 4 → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-box-cP-at0210233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0341 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (pw3 c4 (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (pw3 c4 (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-QVQ-at0210233441 c4) ▸
       at 1 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0210233441 c4) ▸
       at 2 2 [] (lw4 c4 (Toff203 ∷ Toff203 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4-K1-CS0: 19 steps
lem-F4-K1-CS0 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-CS0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ023 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (Bx2-0341 ∷ []) (lem-box-perm-1423-at0210243143 c4) ▸
       at 3 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0210233441 c4) ▸
       at 2 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 1 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 c4) ▸
       at 0 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (CCZ023 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff214 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff214 ∷ []) (Toff214 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 c4) ▸
       at 2 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 4 (Toff214 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff214 ∷ []) (Toff214 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-0341 ∷ []) (sym (lem-box-cP-at0210233441 c4)) ▸
       at 0 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1423-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4-K1-CS1: 17 steps
lem-F4-K1-CS1 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-CS1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 4 (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 c4) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b1 = at 2 4 (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 c4) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- CXbc-box @122441: 17 steps
lem-CXbc-box-at122441 : Complete 4 → ⟪ (CX43 ∷ Bx0-2431 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx0-2431 ∷ CX43 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX43 ∷ CCZ014 ∷ CS14 ∷ CX24 ∷ CS14⁻ ∷ CCZ013 ∷ CX24 ∷ CS12 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (Toff024 ∷ CX43 ∷ []) (pw1 c4 (CX43 ∷ Toff024 ∷ []) (Toff024 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (pw2 c4 (CX43 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ CCZ014 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff024 ∷ CX43 ∷ []) (pw1 c4 (CX43 ∷ Toff024 ∷ []) (Toff024 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ013 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 c4) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX43 ∷ CCZ014 ∷ CS14 ∷ CX24 ∷ CS14⁻ ∷ CCZ013 ∷ CX24 ∷ CS12 ∷ CX43 ∷ []) (Bx0-2431 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 c4) ▸
       at 5 2 (CCZ013 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ124 ∷ []) (lw0 c4 (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (pw2 c4 (CX43 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX43 ∷ []) (pw2 c4 (CX43 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX43 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸ done

  b2 : Chain (Bx0-2431 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ []) (Bx0-2431 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (lw0 c4 (CX43 ∷ CCZ124 ∷ CX43 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @122441: 18 steps
lem-CXcb-box-at122441 : Complete 4 → ⟪ (CX34 ∷ Bx0-2431 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx0-2431 ∷ CX34 ∷ []) (Toff024 ∷ CCZ013 ∷ CX34 ∷ Toff023 ∷ CS13 ∷ CX23 ∷ Toff024 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ CCZ013 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (Toff024 ∷ CX34 ∷ Toff023 ∷ []) (pw1 c4 (CX34 ∷ Toff024 ∷ []) (Toff024 ∷ CX34 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (Toff023 ∷ CCZ013 ∷ []) (CCZ013 ∷ Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CX34 ∷ []) (pw2 c4 (CX34 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff024 ∷ CX23 ∷ []) (pw1 c4 (CX23 ∷ Toff024 ∷ []) (Toff024 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 c4) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CX34 ∷ Toff023 ∷ CS13 ∷ CX23 ∷ Toff024 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ CCZ013 ∷ CX34 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ [])
  b1 = at 5 2 (Toff024 ∷ CX23 ∷ []) (pw1 c4 (CX23 ∷ Toff024 ∷ []) (Toff024 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff024 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF024 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ Toff024 ∷ []) (Toff024 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff024 ∷ CX34 ∷ Toff023 ∷ []) (pw1 c4 (CX34 ∷ Toff024 ∷ []) (Toff024 ∷ CX34 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX34 ∷ []) (pw1 c4 (CX34 ∷ Toff023 ∷ Toff023 ∷ []) (CX34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CX34 ∷ []) (pw2 c4 (CX34 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX34 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (lw0 c4 (CX34 ∷ CCZ123 ∷ CX34 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @122441: 11 steps
lem-SWbc-box-at122441 : Complete 4 → ⟪ (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-SWbc-box-at122441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) (CX43 ∷ Bx0-2431 ∷ CX43 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (lw0 c4 (Sw34 ∷ []) (CX43 ∷ CX34 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (lw0 c4 (Sw34 ∷ []) (CX43 ∷ CX34 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-CXbc-box-at122441 c4) ▸
       at 3 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CX34 ∷ []) (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-CXcb-box-at122441 c4) ▸
       at 4 2 (CX43 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CX43 ∷ []) (CX43 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX43 ∷ []) (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX43 ∷ []) (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX43 ∷ Bx0-2431 ∷ CX43 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) (Bx0-2431 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-CXbc-box-at122441 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @122441: 23 steps
lem-nat-SWbc-at122441 : Complete 4 → ⟪ (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-nat-SWbc-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ Sw34 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 5 2 (Toff204 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ Sw34 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ Sw34 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Sw34 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 8 2 (Toff023 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ023 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff204 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Sw34 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Sw34 ∷ []) (Bx0-2341 ∷ [])
  b2 = at 13 2 (Toff204 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ024 ∷ Sw34 ∷ []) (pw1 c4 (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 16 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx2-041 ∷ []) (refl) ▸
       at 5 6 (Bx2-041 ∷ []) (refl) ▸
       at 0 6 (Bx0-2341 ∷ []) (refl) ▸ done


-- sym-bc @122441: 2 steps
lem-sym-bc-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym-bc-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at122441 c4)) ▸
       at 0 3 (Bx0-2341 ∷ []) (lem-nat-SWbc-at122441 c4) ▸ done


-- box-perm-1324 @122441: 1 steps
lem-box-perm-1324-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-box-perm-1324-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 1 (Bx0-2341 ∷ []) (lem-sym-bc-at122441 c4) ▸ done


-- tP @12233441: 7 steps
lem-tP-at12233441 : Complete 4 → ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ
lem-tP-at12233441 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (lw4 c4 (Toff023 ∷ []) (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (pw2 c4 (Toff014 ∷ []) (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CCZ023 ∷ []) (lem-cQ-at12233441 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff014 ∷ []) (pw2 c4 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (Toff014 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff023 ∷ []) (lw4 c4 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @12233441: 14 steps
lem-VPQ-at12233441 : Complete 4 → ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at12233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (CS14⁻ ∷ CS23⁻ ∷ S0 ∷ Toff014 ∷ Toff023 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (lw4 c4 (Toff023 ∷ CCZ023 ∷ []) (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (pw2 c4 (Toff014 ∷ CCZ014 ∷ []) (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS14⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 c4) ▸
       at 1 2 (CS14⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS14⁻ ∷ CS23⁻ ∷ []) (lw0 c4 (CS23⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at12233441 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS23⁻ ∷ S0 ∷ Toff014 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS23⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑))) ▸
       at 2 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 c4) ▸
       at 3 2 (S0⁻ ∷ CS23⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑))) ▸
       at 0 4 (Toff014 ∷ CCZ014 ∷ []) (pw2 c4 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff023 ∷ CCZ023 ∷ []) (lw4 c4 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @12233441: 3 steps
lem-QVQ-at12233441 : Complete 4 → ⟪ (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-QVQ-at12233441 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ [])
  b0 = at 0 0 (Toff014 ∷ Toff014 ∷ []) (pw2 c4 [] (Toff014 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (sym (lem-VPQ-at12233441 c4)) ▸
       at 4 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸ done

