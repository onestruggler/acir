{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D051 where

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
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-perm-1423)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-box-box-3)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-cP-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D036 using (lem-box-perm-1324-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D042 using (lem-CSdu-box-3-at243243 ; lem-CSu-box-3-at243243 ; lem-F0-at14213243 ; lem-box-perm-1342-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D045 using (lem-box-perm-1423-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D046 using (lem-CSdu-box-3-at0310243142 ; lem-CSu-box-3-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D050 using (lem-box-perm-1342-at243243)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CX14-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CS12-CCZ034 ; lem-comm-CSd12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-comm-CX04-TOFF312)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-comm-CCZ014-CX23 ; lem-comm-TOFF023-CX14 ; lem-comm-TOFF034-CX12)
-- F4-CS1-CS0: 214 steps
lem-F4-CS1-CS0 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-CS0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (run b26))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b0 = at 3 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 3 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 5 1 (CS02 ∷ []) (refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 2 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (pw1 c4 (X4 ∷ CCZ034 ∷ []) (CCZ034 ∷ X4 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) (lw4 c4 (CZ03 ∷ Toff312 ∷ []) (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸ done

  b1 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CCZ034 ∷ CZ03 ∷ CCZ012 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b1 = at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 7 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 7 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CZ03 ∷ []) (pw1 c4 (CZ03 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CCZ034 ∷ CZ03 ∷ CCZ012 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Bx3-0412 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b2 = at 4 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (pw1 c4 (X4 ∷ CCZ034 ∷ []) (CCZ034 ∷ X4 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (X4 ∷ []) (pw1 c4 (X4 ∷ CZ03 ∷ CZ03 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff312 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸
       at 2 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 2 (Bx3-0412 ∷ CS13⁻ ∷ []) (lem-CSdu-box-3-at0310243142 c4) ▸ done

  b3 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Bx3-0412 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b3 = at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 4 2 (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) (pw1 c4 (Toff324 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff312 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ Toff312 ∷ []) (Toff312 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 c4) ▸
       at 8 2 (Toff312 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 c4) ▸
       at 6 2 (Toff312 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ Toff312 ∷ []) (Toff312 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b4 = at 7 5 (CCZ024 ∷ []) (pw1 c4 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff312 ∷ Toff324 ∷ []) (lw0 c4 (Toff324 ∷ Toff312 ∷ []) (Toff312 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ034 ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff312 ∷ Toff324 ∷ []) (lw0 c4 (Toff324 ∷ Toff312 ∷ []) (Toff312 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 3 2 (Bx3-0412 ∷ CS13 ∷ []) (lem-CSu-box-3-at0310243142 c4) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b5 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ CCZ024 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b5 = at 2 2 (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) (pw1 c4 (Toff324 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff312 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ Toff312 ∷ []) (Toff312 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 c4) ▸
       at 6 2 (Toff312 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 c4) ▸
       at 4 2 (Toff312 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ Toff312 ∷ []) (Toff312 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ024 ∷ []) (pw1 c4 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (X4 ∷ Bx0-1423 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ CCZ024 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ Bx0-1234 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b6 = at 3 2 (Toff312 ∷ Toff324 ∷ []) (lw0 c4 (Toff324 ∷ Toff312 ∷ []) (Toff312 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ034 ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff312 ∷ Toff324 ∷ []) (lw0 c4 (Toff324 ∷ Toff312 ∷ []) (Toff312 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-box-perm-1342-at243243 c4) ▸
       at 2 1 (Bx3-0124 ∷ []) (lem-box-perm-1342-at0310243142 c4) ▸
       at 1 2 (Bx3-0124 ∷ Bx0-1234 ∷ []) (lem-box-box-3 c4) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-box-perm-1423-at03102132 c4) ▸ done

  b7 : Chain (X4 ∷ Bx3-0412 ∷ Bx0-1234 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ034 ∷ CX01 ∷ CS02 ∷ Toff312 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b7 = at 2 1 (Bx0-1423 ∷ []) (lem-box-perm-1423 c4) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 0 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (pw1 c4 (X4 ∷ CCZ034 ∷ []) (CCZ034 ∷ X4 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) (lw4 c4 (CZ03 ∷ Toff312 ∷ []) (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ034 ∷ CX01 ∷ CS02 ∷ Toff312 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ X4 ∷ Toff312 ∷ CCZ012 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b8 = at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 5 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 5 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CZ03 ∷ []) (pw1 c4 (CZ03 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (pw1 c4 (X4 ∷ CCZ034 ∷ []) (CCZ034 ∷ X4 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (X4 ∷ []) (pw1 c4 (X4 ∷ CZ03 ∷ CZ03 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff312 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ X4 ∷ Toff312 ∷ CCZ012 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b9 = at 3 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 2 (CCZ014 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ012 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (Bx3-0412 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b10 = at 7 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 6 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 6 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff023 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b11 = at 7 2 (Toff324 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ Toff324 ∷ []) (Toff324 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 5 2 (Toff324 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 2 (Toff324 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ Toff324 ∷ []) (Toff324 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS13 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b12 = at 9 2 (Toff324 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ Toff324 ∷ []) (Toff324 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 7 2 (Toff324 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 5 2 (Toff324 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ Toff324 ∷ []) (Toff324 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS13⁻ ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (X4 ∷ CCZ012 ∷ []) (lw3 c4 (CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX12 ∷ Toff214 ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b13 = at 8 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 2 (CX12 ∷ Toff214 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff214 ∷ []) (CX12 ∷ Toff214 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸
       at 6 1 (CS13⁻ ∷ []) (refl) ▸ done

  b14 : Chain (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX12 ∷ Toff214 ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX12 ∷ K2 ∷ CS24 ∷ CX12 ∷ Toff034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b14 = at 3 6 (CX12 ∷ Toff214 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX12 ∷ Toff214 ∷ []) (CX12 ∷ Toff214 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 2 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 5 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 c4) ▸
       at 7 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K2 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ K2 ∷ []) (K2 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS24 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ CS24 ∷ []) (CS24 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 c4) ▸ done

  b15 : Chain (Bx3-0412 ∷ X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX12 ∷ K2 ∷ CS24 ∷ CX12 ∷ Toff034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ CCZ012 ∷ CX12 ∷ Toff034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b15 = at 9 2 (CS24⁻ ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 c4) ▸
       at 11 2 (CS14 ∷ Toff034 ∷ []) (pw2 c4 (Toff034 ∷ CS14 ∷ []) (CS14 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2⁻ ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CX12 ∷ Toff214 ∷ []) (CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 c4) ▸
       at 5 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸ done

  b16 : Chain (Bx3-0412 ∷ X4 ∷ CCZ012 ∷ CX12 ∷ Toff034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ CCZ012 ∷ CX12 ∷ Toff214 ∷ Toff034 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b16 = at 4 2 (K2 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ K2 ∷ []) (K2 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS24 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ CS24 ∷ []) (CS24 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 c4) ▸
       at 7 2 (CS24⁻ ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 c4) ▸
       at 9 2 (CS14 ∷ Toff034 ∷ []) (pw2 c4 (Toff034 ∷ CS14 ∷ []) (CS14 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K2⁻ ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 4 7 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (Bx3-0412 ∷ X4 ∷ CCZ012 ∷ CX12 ∷ Toff214 ∷ Toff034 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ CX12 ∷ Toff214 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b17 = at 5 2 (CZ01 ∷ CCZ134 ∷ Toff034 ∷ []) (pw2 c4 (Toff034 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ134 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CCZ134 ∷ Toff034 ∷ []) (pw2 c4 (Toff034 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ134 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CZ01 ∷ CCZ014 ∷ []) (pw2 c4 (CZ01 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (CZ01 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 5 (CX12 ∷ Toff214 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ []) (CX12 ∷ Toff214 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-1243 ∷ []) (sym (lem-box-cP-at3443 c4)) ▸
       at 4 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b18 : Chain (Bx3-0412 ∷ X4 ∷ CX12 ∷ Toff214 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CS02 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b18 = at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (Toff214 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX12 ∷ Toff214 ∷ []) (Toff214 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS02 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 7 2 (CS02 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ CS02 ∷ []) (CS02 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS02 ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ CS02 ∷ []) (CS02 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸ done

  b19 : Chain (Bx3-0412 ∷ Toff214 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CS02 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ Sb0-1-42-3 ∷ CX12 ∷ Toff214 ∷ X4 ∷ CS02⁻ ∷ [])
  b19 = at 5 2 (CS02 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ CS02 ∷ []) (CS02 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS02 ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ CS02 ∷ []) (CS02 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS02 ∷ Bx0-1423 ∷ []) (sym (lem-CSu-box-3-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 2 2 (CS02 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX12 ∷ Toff214 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff214 ∷ []) (CX12 ∷ Toff214 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b20 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ Sb0-1-42-3 ∷ CX12 ∷ Toff214 ∷ X4 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX12 ∷ Toff034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ [])
  b20 = at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸
       at 8 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 6 (CX12 ∷ Toff214 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX12 ∷ Toff214 ∷ []) (CX12 ∷ Toff214 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 4 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 7 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 c4) ▸
       at 9 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX12 ∷ Toff034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX12 ∷ Toff214 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ [])
  b21 = at 8 2 (K2 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ K2 ∷ []) (K2 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CS24 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ CS24 ∷ []) (CS24 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 c4) ▸
       at 11 2 (CS24⁻ ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 c4) ▸
       at 13 2 (CS14 ∷ Toff034 ∷ []) (pw2 c4 (Toff034 ∷ CS14 ∷ []) (CS14 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K2⁻ ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 8 7 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸ done

  b22 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX12 ∷ Toff214 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CCZ012 ∷ CX12 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff034 ∷ CS14 ∷ K2⁻ ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ [])
  b22 = at 6 3 (CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CX12 ∷ Toff214 ∷ []) (CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 c4) ▸
       at 7 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K2 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ K2 ∷ []) (K2 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS24 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ CS24 ∷ []) (CS24 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 c4) ▸
       at 9 2 (CS24⁻ ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 c4) ▸ done

  b23 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CCZ012 ∷ CX12 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff034 ∷ CS14 ∷ K2⁻ ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CX12 ∷ Toff214 ∷ Bx0-1243 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ [])
  b23 = at 11 2 (CS14 ∷ Toff034 ∷ []) (pw2 c4 (Toff034 ∷ CS14 ∷ []) (CS14 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K2⁻ ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CZ01 ∷ CCZ134 ∷ Toff034 ∷ []) (pw2 c4 (Toff034 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ134 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CCZ134 ∷ Toff034 ∷ []) (pw2 c4 (Toff034 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ134 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CZ01 ∷ CCZ014 ∷ []) (pw2 c4 (CZ01 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (CZ01 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 5 (CX12 ∷ Toff214 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ []) (CX12 ∷ Toff214 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Bx0-1243 ∷ []) (sym (lem-box-cP-at3443 c4)) ▸ done

  b24 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CX12 ∷ Toff214 ∷ Bx0-1243 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS02⁻ ∷ X4 ∷ [])
  b24 = at 6 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 3 (Toff214 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX12 ∷ Toff214 ∷ []) (Toff214 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS02⁻ ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸ done

  b25 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS02⁻ ∷ X4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ X4 ∷ CS02⁻ ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b25 = at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 9 2 (CS02⁻ ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS02⁻ ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS02⁻ ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS02⁻ ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS02⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CSdu-box-3-at243243 c4)) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b26 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ X4 ∷ CS02⁻ ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b26 = at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 0 1 (Sb2-0-41-3 ∷ []) (sym (lem-F0-at14213243 c4)) ▸ done


-- F4-CS1-CS1: 286 steps
lem-F4-CS1-CS1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-CS1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (pw2 c4 (X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (lw4 c4 (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 10 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 7 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CZ01 ∷ []) (pw2 c4 (CZ01 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (pw2 c4 (X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (lw2 c4 (X4 ∷ CZ01 ∷ CZ01 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CCZ014 ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 6 2 (Toff023 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff023 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ014 ∷ K3⁻ ∷ []) (pw2 c4 (K3⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 7 2 (CCZ014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 5 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ K3 ∷ []) (pw2 c4 (K3 ∷ CCZ014 ∷ []) (CCZ014 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ Toff023 ∷ []) (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b5 = at 13 2 (CCZ014 ∷ K3⁻ ∷ []) (pw2 c4 (K3⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CCZ014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 10 2 (CCZ014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 8 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ K3 ∷ []) (pw2 c4 (K3 ∷ CCZ014 ∷ []) (CCZ014 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 8 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b6 = at 6 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (pw3 c4 (Toff024 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ Toff023 ∷ []) (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Toff023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 10 2 (Toff023 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 8 2 (Toff023 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b7 = at 9 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff023 ∷ Toff024 ∷ []) (pw1 c4 (Toff024 ∷ Toff023 ∷ []) (Toff023 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CCZ124 ∷ []) (pw3 c4 (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 3 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b8 = at 5 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ K3⁻ ∷ []) (pw2 c4 (K3⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸ done

  b9 : Chain (X4 ∷ Bx0-1423 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b9 = at 5 2 (CCZ014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 3 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ K3 ∷ []) (pw2 c4 (K3 ∷ CCZ014 ∷ []) (CCZ014 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 3 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ Toff023 ∷ []) (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ014 ∷ K3⁻ ∷ []) (pw2 c4 (K3⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b10 = at 10 2 (CCZ014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 8 2 (CCZ014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 6 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ K3 ∷ []) (pw2 c4 (K3 ∷ CCZ014 ∷ []) (CCZ014 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (pw3 c4 (Toff024 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b11 = at 7 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (pw1 c4 (Toff324 ∷ Toff023 ∷ []) (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 8 2 (Toff023 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 6 2 (Toff023 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (X4 ∷ Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b12 = at 5 2 (Toff023 ∷ Toff024 ∷ []) (pw1 c4 (Toff024 ∷ Toff023 ∷ []) (Toff023 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ124 ∷ []) (pw3 c4 (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (pw2 c4 (X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (lw4 c4 (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b13 = at 8 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CZ01 ∷ []) (pw2 c4 (CZ01 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (pw2 c4 (X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b14 = at 3 3 (X4 ∷ []) (lw2 c4 (X4 ∷ CZ01 ∷ CZ01 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (Bx0-1423 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b15 = at 4 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 3 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 3 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸ done

  b16 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b16 = at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 8 (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸ done

  b17 : Chain (Bx0-1423 ∷ X4 ∷ Bx0-1423 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b17 = at 3 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸ done

  b18 : Chain (Bx0-1423 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b18 = at 6 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 6 (CX23 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CX20 ∷ CX23 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CX23 ∷ []) (CX20 ∷ CX23 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ Toff324 ∷ []) (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 7 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b19 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b19 = at 10 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K3 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ K3 ∷ []) (K3 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CS34 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 12 2 (CS34⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 14 2 (CS24 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K3⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b20 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b20 = at 9 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX20 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CX20 ∷ []) (CX20 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS24 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS24 ∷ []) (CS24 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸
       at 6 2 (CS24⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸
       at 8 2 (CS12 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS12 ∷ []) (CS12 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ CX23 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ Toff023 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b21 = at 4 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX20 ∷ CX23 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CX23 ∷ []) (CX20 ∷ CX23 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff024 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ Toff024 ∷ []) (Toff024 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS24 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS24 ∷ []) (CS24 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸
       at 10 2 (CS24⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸ done

  b22 : Chain (Bx0-1423 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ CX23 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ Toff023 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CX23 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b22 = at 12 2 (CS12 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS12 ∷ []) (CS12 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 8 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ Toff324 ∷ []) (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CCZ124 ∷ []) (pw3 c4 (CX20 ∷ CCZ124 ∷ CX20 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ124 ∷ []) (pw3 c4 (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (CX23 ∷ Toff324 ∷ []) (lw0 c4 (CCZ124 ∷ CX23 ∷ CCZ124 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 4 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b23 : Chain (Bx0-1423 ∷ X4 ∷ CX23 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CX23 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b23 = at 3 2 (K3 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ K3 ∷ []) (K3 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 6 2 (CS34⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 8 2 (CS24 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K3⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸ done

  b24 : Chain (Bx0-1423 ∷ X4 ∷ CX23 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS13 ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b24 = at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ []) (CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸ done

  b25 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS13 ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b25 = at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 5 (CS13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13 ∷ []) (CS13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (CS13 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS13 ∷ []) (CS13 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS13 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS13 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS13 ∷ []) (CS13 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS13 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b26 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ [])
  b26 = at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ []) (CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX23 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸
       at 8 1 (CS13⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b27 = at 5 6 (CX23 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (CX20 ∷ CX23 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CX23 ∷ []) (CX20 ∷ CX23 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ Toff324 ∷ []) (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 9 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b28 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ K3 ∷ []) (K3 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CS34 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 14 2 (CS34⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 16 2 (CS24 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (K3⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 11 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸ done

  b29 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CX20 ∷ CCZ124 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ Toff023 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b29 = at 5 2 (CX20 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CX20 ∷ []) (CX20 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS24 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS24 ∷ []) (CS24 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸
       at 8 2 (CS24⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸
       at 10 2 (CS12 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS12 ∷ []) (CS12 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b30 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ Toff023 ∷ CX23 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ CX23 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b30 = at 7 2 (CX20 ∷ CX23 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CX23 ∷ []) (CX20 ∷ CX23 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff024 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ Toff024 ∷ []) (Toff024 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CS24 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS24 ∷ []) (CS24 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸
       at 12 2 (CS24⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸
       at 14 2 (CS12 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS12 ∷ []) (CS12 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸ done

  b31 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ014 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ CX23 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b31 = at 10 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ Toff324 ∷ []) (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ124 ∷ []) (pw3 c4 (CX20 ∷ CCZ124 ∷ CX20 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CCZ124 ∷ []) (pw3 c4 (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CX23 ∷ Toff324 ∷ []) (lw0 c4 (CCZ124 ∷ CX23 ∷ CCZ124 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ K3 ∷ []) (K3 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b32 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b32 = at 6 2 (CS34 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b33 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13⁻ ∷ X4 ∷ [])
  b33 = at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 3 (Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13⁻ ∷ X4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b34 = at 6 5 (CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 8 2 (CS13⁻ ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS13⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS13⁻ ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS13⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b35 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b35 = at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

