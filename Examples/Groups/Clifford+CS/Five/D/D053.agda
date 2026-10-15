{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D053 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-cP-at243243 ; lem-tP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-cP-at122441 ; lem-box-tQ-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-tQ-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D031 using (lem-box-perm-1324-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-box-cP-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D052 using (lem-box-perm-3241-at243243 ; lem-box-perm-4213-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX14-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CSd24-TOFF013 ; lem-comm-SWAP23-BOX⟨0·14⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CS24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-comm-CZ13-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-comm-CX23-TOFF014 ; lem-comm-TOFF023-CX14)
-- F4-CS1-CS2: 248 steps
lem-F4-CS1-CS2 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-CS2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (run b30))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (lw4 c4 (CZ02 ∷ Toff013 ∷ []) (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 6 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 8 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CZ02 ∷ []) (pw3 c4 (CZ02 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CCZ024 ∷ CS13⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (lw3 c4 (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸ done

  b3 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CCZ024 ∷ CS13⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff324 ∷ Toff014 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 6 2 (Toff013 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 8 2 (Toff013 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 5 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 4 2 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (pw1 c4 (Toff324 ∷ CCZ023 ∷ []) (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff324 ∷ Toff014 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff014 ∷ K3⁻ ∷ []) (pw2 c4 (K3⁻ ∷ Toff014 ∷ []) (Toff014 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ Toff014 ∷ []) (Toff014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 c4) ▸
       at 8 2 (Toff014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 c4) ▸
       at 6 2 (Toff014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ Toff014 ∷ []) (Toff014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff014 ∷ K3 ∷ []) (pw2 c4 (K3 ∷ Toff014 ∷ []) (Toff014 ∷ K3 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CCZ024 ∷ CCZ023 ∷ CCZ124 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b5 = at 6 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CCZ023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 c4) ▸
       at 10 2 (CCZ023 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 c4) ▸
       at 8 2 (CCZ023 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CCZ024 ∷ CCZ023 ∷ CCZ124 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ Toff014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b6 = at 7 2 (CCZ023 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (pw1 c4 (Toff324 ∷ CCZ023 ∷ []) (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (Toff324 ∷ []) (pw1 c4 (Toff324 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff014 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 13 2 (Toff014 ∷ K3⁻ ∷ []) (pw2 c4 (K3⁻ ∷ Toff014 ∷ []) (Toff014 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Toff014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ Toff014 ∷ []) (Toff014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 c4) ▸ done

  b7 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ Toff014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b7 = at 10 2 (Toff014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 c4) ▸
       at 8 2 (Toff014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ Toff014 ∷ []) (Toff014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff014 ∷ K3 ∷ []) (pw2 c4 (K3 ∷ Toff014 ∷ []) (Toff014 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 8 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 4 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸ done

  b8 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b8 = at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 4 2 (Toff013 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff013 ∷ []) (Toff013 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 6 2 (Toff013 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff013 ∷ []) (Toff013 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 3 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸ done

  b9 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ Toff014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b9 = at 2 2 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (pw1 c4 (Toff324 ∷ CCZ023 ∷ []) (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff014 ∷ K3⁻ ∷ []) (pw2 c4 (K3⁻ ∷ Toff014 ∷ []) (Toff014 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ Toff014 ∷ []) (Toff014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 c4) ▸
       at 6 2 (Toff014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 c4) ▸ done

  b10 : Chain (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ Toff014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CCZ024 ∷ CS24 ∷ CCZ023 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b10 = at 4 2 (Toff014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ Toff014 ∷ []) (Toff014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff014 ∷ K3 ∷ []) (pw2 c4 (K3 ∷ Toff014 ∷ []) (Toff014 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 4 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 c4) ▸
       at 8 2 (CCZ023 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 c4) ▸ done

  b11 : Chain (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CCZ024 ∷ CS24 ∷ CCZ023 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b11 = at 6 2 (CCZ023 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (pw1 c4 (Toff324 ∷ CCZ023 ∷ []) (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff324 ∷ []) (pw1 c4 (Toff324 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff014 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff014 ∷ K3⁻ ∷ []) (pw2 c4 (K3⁻ ∷ Toff014 ∷ []) (Toff014 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Bx0-2341 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b12 = at 10 2 (Toff014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ Toff014 ∷ []) (Toff014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 c4) ▸
       at 8 2 (Toff014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 c4) ▸
       at 6 2 (Toff014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ Toff014 ∷ []) (Toff014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff014 ∷ K3 ∷ []) (pw2 c4 (K3 ∷ Toff014 ∷ []) (Toff014 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸ done

  b13 : Chain (X4 ∷ Bx0-1423 ∷ Bx0-2341 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b13 = at 2 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-box-perm-3241-at243243 c4) ▸
       at 2 1 (Bx0-1423 ∷ []) (lem-box-perm-4213-at122441 c4) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (lw4 c4 (CZ02 ∷ Toff013 ∷ []) (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b14 = at 8 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (pw3 c4 (CZ02 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b15 = at 3 3 (X4 ∷ []) (lw3 c4 (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸ done

  b16 : Chain (Bx0-2431 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b16 = at 4 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 3 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 3 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b17 = at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 8 (Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ []) (Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸ done

  b18 : Chain (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b18 = at 4 3 (CS13 ∷ Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CS13 ∷ Toff324 ∷ []) (CS13 ∷ Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 2 (CX31 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸ done

  b19 : Chain (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b19 = at 6 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 6 (CX31 ∷ Toff134 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX31 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CX31 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CX31 ∷ []) (CX31 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K1 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ K1 ∷ []) (K1 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS34 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS34 ∷ []) (CS34 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸ done

  b20 : Chain (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b20 = at 9 2 (CS34⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸
       at 11 2 (CS13 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS13 ∷ []) (CS13 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1⁻ ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CX31 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX31 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CX31 ∷ []) (CX31 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b21 = at 4 2 (K1 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ K1 ∷ []) (K1 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS34 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS34 ∷ []) (CS34 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸
       at 7 2 (CS34⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸
       at 9 2 (CS13 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS13 ∷ []) (CS13 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K1⁻ ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 4 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸ done

  b22 : Chain (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS12 ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b22 = at 2 3 (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CX31 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b23 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS12 ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b23 = at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 5 (CS12 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS12 ∷ []) (CS12 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (CS12 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS12 ∷ []) (CS12 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS12 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS12 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS12 ∷ []) (CS12 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS12 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b24 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ [])
  b24 = at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX31 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸ done

  b25 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b25 = at 8 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 6 (CX31 ∷ Toff134 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX31 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (CX31 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CX31 ∷ []) (CX31 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K1 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ K1 ∷ []) (K1 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CS34 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS34 ∷ []) (CS34 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸ done

  b26 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b26 = at 11 2 (CS34⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸
       at 13 2 (CS13 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS13 ∷ []) (CS13 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K1⁻ ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 8 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CX31 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX31 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CX31 ∷ []) (CX31 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸ done

  b27 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b27 = at 6 2 (K1 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ K1 ∷ []) (K1 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS34 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS34 ∷ []) (CS34 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸
       at 9 2 (CS34⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 c4) ▸
       at 11 2 (CS13 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS13 ∷ []) (CS13 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1⁻ ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ K1⁻ ∷ []) (K1⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸ done

  b28 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS12⁻ ∷ X4 ∷ [])
  b28 = at 4 3 (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CX31 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 3 (Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b29 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS12⁻ ∷ X4 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b29 = at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 5 (CS12⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (lw0 c4 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS12⁻ ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS12⁻ ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS12⁻ ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b30 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b30 = at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- P-box @122441: 8 steps
lem-P-box-at122441 : Complete 4 → ⟪ (Toff013 ∷ Bx0-2431 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-P-box-at122441 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Bx0-2431 ∷ Toff013 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (Toff024 ∷ Toff013 ∷ []) (sym (lem-tP-at122441 c4)) ▸
       at 1 2 (CCZ013 ∷ CZ13 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CCZ013 ∷ []) (CCZ013 ∷ CZ13 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ Toff013 ∷ []) (sym (lem-tP-at122441 c4)) ▸
       at 4 3 (CCZ013 ∷ CZ13 ∷ []) (lw4 c4 (Toff013 ∷ CCZ013 ∷ Toff013 ∷ []) (CCZ013 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff024 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF024 c4) ▸
       at 3 3 (CCZ013 ∷ []) (lw4 c4 (CZ13 ∷ CCZ013 ∷ CZ13 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸ done


-- pairs @122441: 4 steps
lem-pairs-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-pairs-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 1 (Toff013 ∷ Bx0-2431 ∷ Toff013 ∷ []) (sym (lem-P-box-at122441 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 [] (lw4 c4 (Toff013 ∷ Toff013 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-3124 ∷ []) (sym (lem-box-tQ-at132132 c4)) ▸ done


-- sym-ab @132132: 18 steps
lem-sym-ab-at132132 : Complete 4 → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym-ab-at132132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3124 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw1 c4 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (pw3 c4 (CCZ024 ∷ []) (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-14 ∷ []) (refl) ▸
       at 7 1 (Bx0-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ [])
  b1 = at 2 6 (Bx1-024 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (pw1 c4 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (pw3 c4 (CCZ024 ∷ []) (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-14 ∷ []) (refl) ▸
       at 10 1 (Bx0-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (Bx0-1324 ∷ [])
  b2 = at 5 6 (Bx1-024 ∷ []) (refl) ▸
       at 0 6 (Bx0-1324 ∷ []) (refl) ▸ done


-- CXbc-box @2332: 17 steps
lem-CXbc-box-at2332 : Complete 4 → ⟪ (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at2332 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX32 ∷ CCZ034 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ CX32 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at2332 c4) ▸
       at 0 2 (Toff013 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ Toff013 ∷ []) (Toff013 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (pw1 c4 (CX32 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ CCZ034 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ034 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ Toff013 ∷ []) (Toff013 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX32 ∷ CCZ034 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ CX32 ∷ []) (Bx0-1324 ∷ CX32 ∷ CCZ134 ∷ CX32 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (pw1 c4 (CX32 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX32 ∷ []) (pw1 c4 (CX32 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX32 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1324 ∷ []) (sym (lem-box-tQ-at2332 c4)) ▸ done

  b2 : Chain (Bx0-1324 ∷ CX32 ∷ CCZ134 ∷ CX32 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (lw0 c4 (CX32 ∷ CCZ134 ∷ CX32 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @2332: 18 steps
lem-CXcb-box-at2332 : Complete 4 → ⟪ (CX23 ∷ Bx0-1324 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at2332 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx0-1324 ∷ CX23 ∷ []) (Toff013 ∷ CCZ024 ∷ CX23 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ Toff013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ CX23 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at2332 c4) ▸
       at 0 2 (Toff013 ∷ CX23 ∷ Toff012 ∷ []) (lw4 c4 (CX23 ∷ Toff013 ∷ []) (Toff013 ∷ CX23 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ Toff012 ∷ CCZ124 ∷ []) (pw3 c4 (Toff012 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX23 ∷ []) (pw1 c4 (CX23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff013 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ Toff013 ∷ []) (Toff013 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 c4) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ CX23 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ Toff013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ CX23 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX23 ∷ CCZ124 ∷ CX23 ∷ [])
  b1 = at 5 2 (Toff013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 c4) ▸
       at 5 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ Toff013 ∷ []) (Toff013 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ CX23 ∷ Toff012 ∷ []) (lw4 c4 (CX23 ∷ Toff013 ∷ []) (Toff013 ∷ CX23 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX23 ∷ []) (lw4 c4 (CX23 ∷ Toff012 ∷ Toff012 ∷ []) (CX23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX23 ∷ []) (pw1 c4 (CX23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX23 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX23 ∷ CCZ124 ∷ CX23 ∷ []) (Bx0-1324 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx0-1324 ∷ []) (sym (lem-box-tQ-at2332 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (lw0 c4 (CX23 ∷ CCZ124 ∷ CX23 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @2332: 11 steps
lem-SWbc-box-at2332 : Complete 4 → ⟪ (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-SWbc-box-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) (CX32 ∷ Bx0-1324 ∷ CX32 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX32 ∷ CX23 ∷ CX32 ∷ []) (lw4 c4 (Sw23 ∷ []) (CX32 ∷ CX23 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX32 ∷ CX23 ∷ CX32 ∷ []) (lw4 c4 (Sw23 ∷ []) (CX32 ∷ CX23 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CXbc-box-at2332 c4) ▸
       at 3 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX23 ∷ []) (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1324 ∷ CCZ124 ∷ []) (lem-CXcb-box-at2332 c4) ▸
       at 4 2 (CX32 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX32 ∷ Bx0-1324 ∷ CX32 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) (Bx0-1324 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CXbc-box-at2332 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @2332: 23 steps
lem-nat-SWbc-at2332 : Complete 4 → ⟪ (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-nat-SWbc-at2332 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ Sw23 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ c4) ▸
       at 5 2 (Toff103 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ Sw23 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ Sw23 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Sw23 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ c4) ▸
       at 8 2 (Toff012 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff103 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ c4) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Sw23 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Sw23 ∷ []) (Bx0-1234 ∷ [])
  b2 = at 13 2 (Toff103 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ013 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ c4) ▸
       at 16 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx1-034 ∷ []) (refl) ▸
       at 5 6 (Bx1-034 ∷ []) (refl) ▸
       at 0 6 (Bx0-1234 ∷ []) (refl) ▸ done


-- sym-bc @2332: 2 steps
lem-sym-bc-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym-bc-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) (sym (lem-SWbc-box-at2332 c4)) ▸
       at 0 3 (Bx0-1234 ∷ []) (lem-nat-SWbc-at2332 c4) ▸ done


-- box-perm-4132 @122441: 3 steps
lem-box-perm-4132-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-4132-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-3124 ∷ []) (lem-pairs-at122441 c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym-ab-at132132 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym-bc-at2332 c4) ▸ done

