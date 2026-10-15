{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D046 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at0210243143 ; lem-box-tQ-at0210243143 ; lem-tP-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-cP-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D036 using (lem-box-perm-1324-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D042 using (lem-CSdu-box-3-at243243 ; lem-CSu-box-3-at243243 ; lem-F0-at14213243 ; lem-box-perm-1342-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D043 using (lem-box-perm-4132-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D045 using (lem-box-box-1-at03102132 ; lem-box-perm-1423-at03102132 ; lem-box-perm-2431-at132132)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX12-CCZ034 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CZ13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CS12-CCZ034 ; lem-comm-CSd12-CCZ034 ; lem-comm-CX12-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CS04-TOFF213)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-comm-CX04-TOFF312)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-comm-CCZ134-CS02 ; lem-comm-CZ13-TOFF204 ; lem-comm-SWAP03-BOX⟨2·14⟩ ; lem-comm-TOFF312-CX04)
-- CXu-box-4 @0310243142: 15 steps
lem-CXu-box-4-at0310243142 : Complete 4 → ⟪ (CX23 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CX23 ∷ []) ⟫ʷ
lem-CXu-box-4-at0310243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX23 ∷ Bx3-0412 ∷ []) (CCZ034 ∷ CX23 ∷ Toff312 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 0 2 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (pw1 c4 (CX23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff312 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ Toff312 ∷ []) (Toff312 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 c4) ▸
       at 4 2 (Toff312 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 c4) ▸
       at 2 2 (Toff312 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ Toff312 ∷ []) (Toff312 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ034 ∷ CX23 ∷ Toff312 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ []) (Bx3-0412 ∷ CX23 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (pw1 c4 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ Toff312 ∷ []) (Toff312 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (pw1 c4 (CX23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX23 ∷ []) (pw1 c4 (CX23 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ Toff312 ∷ []) (Toff312 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done


-- CSu-box-3 @0310243142: 17 steps
lem-CSu-box-3-at0310243142 : Complete 4 → ⟪ (CS13 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CS13 ∷ []) ⟫ʷ
lem-CSu-box-3-at0310243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS13 ∷ Bx3-0412 ∷ []) (CCZ034 ∷ Toff312 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CCZ034 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff312 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 0 2 (CCZ034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ []) (lw4 c4 (CS13 ∷ Toff312 ∷ []) (Toff312 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CX31 ∷ []) (pw2 c4 (CX31 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 5 2 (CCZ034 ∷ CX31 ∷ []) (pw2 c4 (CX31 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX31 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff312 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CCZ034 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff312 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ [])
  b1 = at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff312 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff312 ∷ []) (Toff312 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ []) (lw4 c4 (CS13 ∷ Toff312 ∷ []) (Toff312 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS13 ∷ []) (lw4 c4 (CS13 ∷ CS12 ∷ CCZ123 ∷ CS12 ∷ CZ12 ∷ CCZ123 ∷ []) (CS13 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ []) (Bx3-0412 ∷ CS13 ∷ [])
  b2 = at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done


-- CSdu-box-3 @0310243142: 17 steps
lem-CSdu-box-3-at0310243142 : Complete 4 → ⟪ (CS13⁻ ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0310243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS13⁻ ∷ Bx3-0412 ∷ []) (CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CS12 ∷ CCZ034 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff312 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 0 2 (CCZ034 ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ []) (lw4 c4 (CS13⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CX31 ∷ []) (pw2 c4 (CX31 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 5 2 (CCZ034 ∷ CX31 ∷ []) (pw2 c4 (CX31 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX31 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CS12 ∷ CCZ034 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff312 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ [])
  b1 = at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff312 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ []) (lw4 c4 (CS13⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ CS12⁻ ∷ CZ12 ∷ CCZ123 ∷ []) (CS13⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ []) (Bx3-0412 ∷ CS13⁻ ∷ [])
  b2 = at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done


-- F4-CS0-CS1: 232 steps
lem-F4-CS0-CS1 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-CS1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (run b28))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb3-0-41-2 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (pw2 c4 (X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (lw4 c4 (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (X4 ∷ Sb3-0-41-2 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Sb3-0-41-2 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ014 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 7 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CZ01 ∷ []) (pw2 c4 (CZ01 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (X4 ∷ Sb3-0-41-2 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ014 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Bx0-1423 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 4 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (pw2 c4 (X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (X4 ∷ []) (lw2 c4 (X4 ∷ CZ01 ∷ CZ01 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 5 1 (CS02⁻ ∷ []) (refl) ▸
       at 5 2 (Bx0-1423 ∷ CS02⁻ ∷ []) (lem-CSdu-box-3-at243243 c4) ▸ done

  b3 : Chain (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Bx0-1423 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 5 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 5 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 4 2 (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) (pw3 c4 (Toff214 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff034 ∷ CCZ014 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ014 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff034 ∷ K2⁻ ∷ []) (pw1 c4 (K2⁻ ∷ Toff034 ∷ []) (Toff034 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff034 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ Toff034 ∷ []) (Toff034 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 c4) ▸ done

  b4 : Chain (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ Toff034 ∷ Toff214 ∷ CCZ014 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ012 ∷ CX13 ∷ CS14 ∷ Toff034 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 8 2 (Toff034 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 c4) ▸
       at 6 2 (Toff034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ Toff034 ∷ []) (Toff034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff034 ∷ K2 ∷ []) (pw1 c4 (K2 ∷ Toff034 ∷ []) (Toff034 ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CCZ012 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ Toff034 ∷ Toff214 ∷ CCZ014 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ012 ∷ CX13 ∷ CS14 ∷ Toff034 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff214 ∷ Toff034 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b5 = at 10 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 9 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 9 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ012 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) (pw3 c4 (Toff214 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (Toff214 ∷ []) (pw3 c4 (Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff034 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff214 ∷ Toff034 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b6 = at 7 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 13 2 (Toff034 ∷ K2⁻ ∷ []) (pw1 c4 (K2⁻ ∷ Toff034 ∷ []) (Toff034 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Toff034 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ Toff034 ∷ []) (Toff034 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 c4) ▸
       at 10 2 (Toff034 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 c4) ▸
       at 8 2 (Toff034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ Toff034 ∷ []) (Toff034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff034 ∷ K2 ∷ []) (pw1 c4 (K2 ∷ Toff034 ∷ []) (Toff034 ∷ K2 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ Toff214 ∷ CCZ014 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b7 = at 8 7 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-1243 ∷ []) (sym (lem-box-cP-at3443 c4)) ▸
       at 4 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 3 1 (CS02 ∷ []) (refl) ▸
       at 3 2 (Bx0-1423 ∷ CS02 ∷ []) (lem-CSu-box-3-at243243 c4) ▸
       at 3 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 3 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 2 2 (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) (pw3 c4 (Toff214 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ Toff214 ∷ CCZ014 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ K2 ∷ Toff034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b8 = at 4 2 (Toff034 ∷ CCZ014 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ014 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff034 ∷ K2⁻ ∷ []) (pw1 c4 (K2⁻ ∷ Toff034 ∷ []) (Toff034 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff034 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ Toff034 ∷ []) (Toff034 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 c4) ▸
       at 6 2 (Toff034 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 c4) ▸
       at 4 2 (Toff034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ Toff034 ∷ []) (Toff034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ K2 ∷ Toff034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ Toff034 ∷ Toff214 ∷ CCZ014 ∷ CCZ012 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b9 = at 3 2 (Toff034 ∷ K2 ∷ []) (pw1 c4 (K2 ∷ Toff034 ∷ []) (Toff034 ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 4 7 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ012 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸ done

  b10 : Chain (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ Toff034 ∷ Toff214 ∷ CCZ014 ∷ CCZ012 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff034 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b10 = at 7 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) (pw3 c4 (Toff214 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff214 ∷ []) (pw3 c4 (Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff034 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff034 ∷ K2⁻ ∷ []) (pw1 c4 (K2⁻ ∷ Toff034 ∷ []) (Toff034 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff034 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ Toff034 ∷ []) (Toff034 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff034 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ Bx0-1423 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b11 = at 9 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 c4) ▸
       at 8 2 (Toff034 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 c4) ▸
       at 6 2 (Toff034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ Toff034 ∷ []) (Toff034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff034 ∷ K2 ∷ []) (pw1 c4 (K2 ∷ Toff034 ∷ []) (Toff034 ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx0-1243 ∷ []) (sym (lem-box-cP-at3443 c4)) ▸
       at 2 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸ done

  b12 : Chain (X4 ∷ Bx3-0412 ∷ Bx0-1423 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ014 ∷ X4 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ Bx3-0412 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b12 = at 1 1 (Bx3-0124 ∷ []) (lem-box-perm-1342-at0310243142 c4) ▸
       at 2 1 (Bx0-3124 ∷ []) (lem-box-perm-4132-at243243 c4) ▸
       at 1 2 (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-box-box-1-at03102132 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-box-perm-2431-at132132 c4) ▸
       at 2 1 (Bx3-0412 ∷ []) (lem-box-perm-1423-at03102132 c4) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (pw2 c4 (X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (lw4 c4 (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (CCZ014 ∷ X4 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ Bx3-0412 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CCZ014 ∷ CCZ123 ∷ Toff023 ∷ Bx3-0412 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b13 = at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CCZ014 ∷ CCZ123 ∷ Toff023 ∷ Bx3-0412 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b14 = at 3 2 (CCZ014 ∷ CZ01 ∷ []) (pw2 c4 (CZ01 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (pw2 c4 (X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (X4 ∷ []) (lw2 c4 (X4 ∷ CZ01 ∷ CZ01 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (Bx0-1423 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ034 ∷ Toff312 ∷ CZ12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b15 = at 6 2 (CCZ034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 4 2 (CCZ034 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 3 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸ done

  b16 : Chain (Bx0-1423 ∷ X4 ∷ CCZ034 ∷ Toff312 ∷ CZ12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b16 = at 9 2 (CCZ034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 7 2 (CCZ034 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 5 2 (CCZ034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 c4) ▸
       at 5 3 (Toff312 ∷ CCZ123 ∷ []) (lw4 c4 (CZ12 ∷ CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (Bx0-1423 ∷ X4 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b17 = at 2 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 3 3 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ123 ∷ Toff214 ∷ CCZ134 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CS02 c4) ▸
       at 5 2 (CS02 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CS02 ∷ []) (CS02 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CCZ134 ∷ Toff214 ∷ CCZ134 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS02⁻ ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸ done

  b18 : Chain (Bx0-1423 ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b18 = at 4 2 (CS02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CS02 c4) ▸
       at 5 2 (Toff214 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 6 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 2 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸ done

  b19 : Chain (Bx0-1423 ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff324 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b19 = at 4 1 (CS02 ∷ []) (refl) ▸
       at 6 1 (CS02⁻ ∷ []) (refl) ▸
       at 6 3 (CX23 ∷ Toff324 ∷ CS02⁻ ∷ []) (pw1 c4 (CS02⁻ ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX23 ∷ Toff324 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX23 ∷ Toff324 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX23 ∷ Toff324 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX23 ∷ Bx3-0412 ∷ []) (sym (lem-CXu-box-4-at0310243142 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b20 : Chain (Bx0-1423 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff324 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ Toff312 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b20 = at 6 2 (Toff324 ∷ Toff312 ∷ []) (lw0 c4 (Toff312 ∷ Toff324 ∷ []) (Toff324 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff324 ∷ Toff312 ∷ []) (lw0 c4 (Toff312 ∷ Toff324 ∷ []) (Toff324 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS24 ∷ Toff312 ∷ []) (lw0 c4 (Toff312 ∷ CS24 ∷ []) (CS24 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 c4) ▸
       at 7 2 (CS24⁻ ∷ Toff312 ∷ []) (lw0 c4 (Toff312 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 c4) ▸ done

  b21 : Chain (Bx0-1423 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ Toff312 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Sb3-0-41-2 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b21 = at 9 2 (CS02 ∷ Toff312 ∷ []) (lw4 c4 (Toff312 ∷ CS02 ∷ []) (CS02 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ024 ∷ []) (pw1 c4 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff324 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) (Toff324 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 6 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 4 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 1 3 (Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b22 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Sb3-0-41-2 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Bx3-0412 ∷ CS13 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b22 = at 4 2 (CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ []) (CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 5 1 (CS02 ∷ []) (refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 7 2 (CS13 ∷ CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ CS13 ∷ []) (CS13 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS13 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ CS13 ∷ []) (CS13 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS13 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CS13 ∷ []) (CS13 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS13 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ CS13 ∷ []) (CS13 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸ done

  b23 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Bx3-0412 ∷ CS13 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ [])
  b23 = at 3 2 (CS13 ∷ Bx3-0412 ∷ []) (sym (lem-CSu-box-3-at0310243142 c4)) ▸
       at 6 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 4 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ []) (CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX23 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 6 1 (CS02 ∷ []) (refl) ▸ done

  b24 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b24 = at 8 1 (CS02⁻ ∷ []) (refl) ▸
       at 8 3 (CX23 ∷ Toff324 ∷ CS02⁻ ∷ []) (pw1 c4 (CS02⁻ ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CX23 ∷ Toff324 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CX23 ∷ Toff324 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX23 ∷ Toff324 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX23 ∷ Bx3-0412 ∷ []) (sym (lem-CXu-box-4-at0310243142 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 8 2 (Toff324 ∷ Toff312 ∷ []) (lw0 c4 (Toff312 ∷ Toff324 ∷ []) (Toff324 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸ done

  b25 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b25 = at 7 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff324 ∷ Toff312 ∷ []) (lw0 c4 (Toff312 ∷ Toff324 ∷ []) (Toff324 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS24 ∷ Toff312 ∷ []) (lw0 c4 (Toff312 ∷ CS24 ∷ []) (CS24 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 c4) ▸
       at 9 2 (CS24⁻ ∷ Toff312 ∷ []) (lw0 c4 (Toff312 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 c4) ▸
       at 11 2 (CS02 ∷ Toff312 ∷ []) (lw4 c4 (Toff312 ∷ CS02 ∷ []) (CS02 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸ done

  b26 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ Sb3-0-41-2 ∷ CS13⁻ ∷ X4 ∷ [])
  b26 = at 7 5 (CCZ024 ∷ []) (pw1 c4 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff324 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) (Toff324 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 8 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 6 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 3 3 (Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b27 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ Sb3-0-41-2 ∷ CS13⁻ ∷ X4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ [])
  b27 = at 5 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 7 1 (CS02 ∷ []) (refl) ▸
       at 9 1 (CS02⁻ ∷ []) (refl) ▸
       at 9 2 (CS13⁻ ∷ CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS13⁻ ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS13⁻ ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS13⁻ ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS13⁻ ∷ Bx3-0412 ∷ []) (sym (lem-CSdu-box-3-at0310243142 c4)) ▸ done

  b28 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b28 = at 8 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 6 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 2 1 (Sb2-0-41-3 ∷ []) (sym (lem-F0-at14213243 c4)) ▸ done


-- CSdu-box-3 @122441: 17 steps
lem-CSdu-box-3-at122441 : Complete 4 → ⟪ (CS03⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03⁻ ∷ Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ CS13⁻ ∷ CS13 ∷ CCZ024 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff013 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ CS03⁻ ∷ []) (pw1 c4 (CS03⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CS03⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX03 ∷ []) (pw1 c4 (CX03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CX03 ∷ []) (pw1 c4 (CX03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ CS13⁻ ∷ CS13 ∷ CCZ024 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff013 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ [])
  b1 = at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 5 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS03⁻ ∷ []) (pw1 c4 (CS03⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ []) (lw4 c4 (CS03⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ []) (CS03⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ []) (Bx0-2431 ∷ CS03⁻ ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done


-- CSu-box-3 @122441: 17 steps
lem-CSu-box-3-at122441 : Complete 4 → ⟪ (CS03 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS03 ∷ []) ⟫ʷ
lem-CSu-box-3-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03 ∷ Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CS03 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff013 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ []) (lw4 c4 (CS03 ∷ Toff013 ∷ []) (Toff013 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX03 ∷ []) (pw1 c4 (CX03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CX03 ∷ []) (pw1 c4 (CX03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CS03 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff013 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03 ∷ [])
  b1 = at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 5 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff013 ∷ []) (Toff013 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ []) (lw4 c4 (CS03 ∷ Toff013 ∷ []) (Toff013 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS03 ∷ []) (lw4 c4 (CS03 ∷ CS13 ∷ CCZ013 ∷ CS13 ∷ CZ13 ∷ CCZ013 ∷ []) (CS03 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03 ∷ []) (Bx0-2431 ∷ CS03 ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done


-- P-box @0210243143: 8 steps
lem-P-box-at0210243143 : Complete 4 → ⟪ (Toff213 ∷ Bx2-0413 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-P-box-at0210243143 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Bx2-0413 ∷ Toff213 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (Toff204 ∷ Toff213 ∷ []) (sym (lem-tP-at0210243143 c4)) ▸
       at 1 2 (CCZ123 ∷ CZ13 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CCZ123 ∷ []) (CCZ123 ∷ CZ13 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff204 ∷ Toff213 ∷ []) (sym (lem-tP-at0210243143 c4)) ▸
       at 4 3 (CCZ123 ∷ CZ13 ∷ []) (lw4 c4 (Toff213 ∷ CCZ123 ∷ Toff213 ∷ []) (CCZ123 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff204 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF204 c4) ▸
       at 3 3 (CCZ123 ∷ []) (lw4 c4 (CZ13 ∷ CCZ123 ∷ CZ13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸ done


-- cQ @022330: 7 steps
lem-cQ-at022330 : Complete 4 → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at022330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 0 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @022330: 13 steps
lem-box-tQ-at022330 : Complete 4 → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at022330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1304 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw3 c4 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (pw3 c4 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) (lw4 c4 (CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 c4) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at022330 c4) ▸
       at 2 4 (Toff213 ∷ []) (lw4 c4 (CCZ123 ∷ CZ13 ∷ Toff213 ∷ CCZ123 ∷ []) (Toff213 ∷ []) tt tt Eq.refl) ▸ done


-- pairs @0210243143: 4 steps
lem-pairs-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-pairs-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 0 1 (Toff213 ∷ Bx2-0413 ∷ Toff213 ∷ []) (sym (lem-P-box-at0210243143 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 [] (lw4 c4 (Toff213 ∷ Toff213 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx2-1304 ∷ []) (sym (lem-box-tQ-at022330 c4)) ▸ done


-- CXbc-box @022330: 17 steps
lem-CXbc-box-at022330 : Complete 4 → ⟪ (CX30 ∷ Bx2-1304 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at022330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX30 ∷ Bx2-1304 ∷ CX30 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX30 ∷ CCZ234 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ CX30 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at022330 c4) ▸
       at 0 2 (Toff213 ∷ CX30 ∷ []) (lw4 c4 (CX30 ∷ Toff213 ∷ []) (Toff213 ∷ CX30 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX30 ∷ CCZ234 ∷ []) (pw1 c4 (CX30 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX30 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ CCZ234 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ234 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ234 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff213 ∷ CX30 ∷ []) (lw4 c4 (CX30 ∷ Toff213 ∷ []) (Toff213 ∷ CX30 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX30 ∷ CCZ234 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ CX30 ∷ []) (Bx2-1304 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX30 ∷ CCZ234 ∷ []) (pw1 c4 (CX30 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX30 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX30 ∷ []) (pw1 c4 (CX30 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX30 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-1304 ∷ []) (sym (lem-box-tQ-at022330 c4)) ▸ done

  b2 : Chain (Bx2-1304 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ []) (Bx2-1304 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (pw2 c4 (CX30 ∷ CCZ134 ∷ CX30 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @022330: 18 steps
lem-CXcb-box-at022330 : Complete 4 → ⟪ (CX03 ∷ Bx2-1304 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at022330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX03 ∷ Bx2-1304 ∷ CX03 ∷ []) (Toff213 ∷ CCZ024 ∷ CX03 ∷ Toff201 ∷ CS04 ∷ CX10 ∷ Toff213 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ CCZ024 ∷ CX03 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at022330 c4) ▸
       at 0 2 (Toff213 ∷ CX03 ∷ Toff201 ∷ []) (lw4 c4 (CX03 ∷ Toff213 ∷ []) (Toff213 ∷ CX03 ∷ Toff201 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (pw3 c4 (Toff201 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX03 ∷ []) (pw1 c4 (CX03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff213 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff213 ∷ CX10 ∷ []) (lw4 c4 (CX10 ∷ Toff213 ∷ []) (Toff213 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 c4) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ CX03 ∷ Toff201 ∷ CS04 ∷ CX10 ∷ Toff213 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ CCZ024 ∷ CX03 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ [])
  b1 = at 5 2 (Toff213 ∷ CX10 ∷ []) (lw4 c4 (CX10 ∷ Toff213 ∷ []) (Toff213 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 c4) ▸
       at 5 5 (CCZ014 ∷ []) (pw2 c4 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ Toff201 ∷ []) (lw4 c4 (Toff201 ∷ Toff213 ∷ []) (Toff213 ∷ Toff201 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff213 ∷ CX03 ∷ Toff201 ∷ []) (lw4 c4 (CX03 ∷ Toff213 ∷ []) (Toff213 ∷ CX03 ∷ Toff201 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX03 ∷ []) (lw4 c4 (CX03 ∷ Toff201 ∷ Toff201 ∷ []) (CX03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX03 ∷ []) (pw1 c4 (CX03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ []) (Bx2-1304 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx2-1304 ∷ []) (sym (lem-box-tQ-at022330 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (pw2 c4 (CX03 ∷ CCZ014 ∷ CX03 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @022330: 11 steps
lem-SWbc-box-at022330 : Complete 4 → ⟪ (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-SWbc-box-at022330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) (CX30 ∷ Bx2-1304 ∷ CX30 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX30 ∷ CX03 ∷ CX30 ∷ []) (lw4 c4 (Sw03 ∷ []) (CX30 ∷ CX03 ∷ CX30 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX30 ∷ CX03 ∷ CX30 ∷ []) (lw4 c4 (Sw03 ∷ []) (CX30 ∷ CX03 ∷ CX30 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx2-1304 ∷ CCZ134 ∷ []) (lem-CXbc-box-at022330 c4) ▸
       at 3 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx2-1304 ∷ CCZ014 ∷ []) (lem-CXcb-box-at022330 c4) ▸
       at 4 2 (CX30 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX30 ∷ Bx2-1304 ∷ CX30 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (Bx2-1304 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx2-1304 ∷ CCZ134 ∷ []) (lem-CXbc-box-at022330 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @022330: 23 steps
lem-nat-SWbc-at022330 : Complete 4 → ⟪ (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-nat-SWbc-at022330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ Sw03 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ CCZ123 ∷ []) (CCZ012 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ Toff213 ∷ []) (Toff201 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ CCZ012 ∷ []) (CCZ123 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff123 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ Toff102 ∷ []) (Toff123 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ c4) ▸
       at 5 2 (Toff123 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ Toff102 ∷ []) (Toff123 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ Sw03 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ Sw03 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Sw03 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Sw03 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ CCZ012 ∷ []) (CCZ123 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ c4) ▸
       at 8 2 (Toff201 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ Toff213 ∷ []) (Toff201 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ CCZ123 ∷ []) (CCZ012 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ CCZ012 ∷ []) (CCZ123 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff123 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ Toff102 ∷ []) (Toff123 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ c4) ▸ done

  b2 : Chain (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Sw03 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Sw03 ∷ []) (Bx2-1034 ∷ [])
  b2 = at 13 2 (Toff123 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ Toff102 ∷ []) (Toff123 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ123 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ CCZ012 ∷ []) (CCZ123 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ c4) ▸
       at 16 2 [] (lw4 c4 (Sw03 ∷ Sw03 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx1-234 ∷ []) (refl) ▸
       at 5 6 (Bx1-234 ∷ []) (refl) ▸
       at 0 6 (Bx2-1034 ∷ []) (refl) ▸ done


-- sym-bc @022330: 2 steps
lem-sym-bc-at022330 : Complete 4 → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-sym-bc-at022330 c4 = run b0
  where
  b0 : Chain (Bx2-1304 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 0 1 (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) (sym (lem-SWbc-box-at022330 c4)) ▸
       at 0 3 (Bx2-1034 ∷ []) (lem-nat-SWbc-at022330 c4) ▸ done


-- sym-ab @0220: 18 steps
lem-sym-ab-at0220 : Complete 4 → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym-ab-at0220 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-1034 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (pw1 c4 (CCZ234 ∷ []) (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx2-04 ∷ []) (refl) ▸
       at 7 1 (Bx2-04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ [])
  b1 = at 2 6 (Bx0-234 ∷ []) (refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (pw1 c4 (CCZ234 ∷ []) (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx2-04 ∷ []) (refl) ▸
       at 10 1 (Bx2-04 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (Bx2-0134 ∷ [])
  b2 = at 5 6 (Bx0-234 ∷ []) (refl) ▸
       at 0 6 (Bx2-0134 ∷ []) (refl) ▸ done

