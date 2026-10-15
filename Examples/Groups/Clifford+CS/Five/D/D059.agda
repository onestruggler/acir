{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D059 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-F5-01)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-box-tQ-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D036 using (lem-box-perm-1324-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D050 using (lem-F4-CS0-CS2)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024)
-- F2-K3-CS1: 35 steps
lem-F2-K3-CS1 : Complete 4 → ⟪ (CK43 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-F2-K3-CS1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CK43 ∷ Sb0-1-42-3 ∷ []) (Toff012 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ Toff012 ∷ CZ03 ∷ CCZ123 ∷ CCZ034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4) ▸
       at 0 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 1 2 (CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ []) (pw1 c4 (CK43 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ CZ03 ∷ CCZ123 ∷ []) (lw4 c4 (CZ03 ∷ Toff012 ∷ []) (Toff012 ∷ CZ03 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ Toff012 ∷ CZ03 ∷ CCZ123 ∷ CCZ034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CZ03 ∷ CCZ123 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 3 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 2 2 (Toff012 ∷ CZ03 ∷ CCZ123 ∷ []) (lw4 c4 (CZ03 ∷ Toff012 ∷ []) (Toff012 ∷ CZ03 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 9 2 (CCZ034 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 7 2 (CCZ034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CZ03 ∷ CCZ123 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CZ03 ∷ CS23 ∷ CCZ034 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ CZ03 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 8 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CZ03 ∷ []) (pw1 c4 (CZ03 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ []) (pw1 c4 (CK43 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 6 2 (CCZ034 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸ done

  b3 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CZ03 ∷ CS23 ∷ CCZ034 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ CZ03 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK43 ∷ [])
  b3 = at 4 2 (CCZ034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CZ03 ∷ []) (pw1 c4 (CZ03 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CZ03 ∷ CK43 ∷ []) (pw1 c4 (CZ03 ∷ CK43 ∷ CZ03 ∷ CZ03 ∷ []) (CZ03 ∷ CK43 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ123 ∷ []) (lw4 c4 (CZ03 ∷ CCZ123 ∷ CZ03 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸
       at 0 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK43 ∷ []) (lw0 c4 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK43 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK43 ∷ []) (Sb0-1-42-3 ∷ CK43 ∷ [])
  b4 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- inv-SBOX(2;0;41;3): 30 steps
lem-inv-SBOX⟨2·0·41·3⟩ : Complete 4 → ⟪ (Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-inv-SBOX⟨2·0·41·3⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CS03⁻ ∷ Toff314 ∷ Bx⁻2-0413 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 4 2 [] (lw4 c4 (CS03⁻ ∷ CS03 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 3 1 (CS03⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CS03⁻ ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ [])
  b1 = at 2 2 [] (lw4 c4 (CS03 ∷ CS03⁻ ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸
       at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 6 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 11 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ [])
  b2 = at 11 1 (CZ03 ∷ []) (refl) ▸
       at 14 1 (CZ03 ∷ []) (refl) ▸
       at 5 12 [] (lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸ done

  b3 : Chain (CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) []
  b3 = at 8 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 8 1 (CZ03 ∷ []) (refl) ▸
       at 11 1 (CZ03 ∷ []) (refl) ▸
       at 2 12 [] (lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸ done


-- invr-SBOX(2;0;41;3): 30 steps
lem-invr-SBOX⟨2·0·41·3⟩ : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-invr-SBOX⟨2·0·41·3⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 0 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 10 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 9 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 7 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 10 1 (CZ03 ∷ []) (refl) ▸
       at 13 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 18 1 (CZ03 ∷ []) (refl) ▸
       at 7 12 [] (lw4 c4 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸ done

  b2 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b2 = at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 12 1 (CZ03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 4 12 [] (lw4 c4 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸
       at 2 1 (CS03⁻ ∷ []) (refl) ▸ done

  b3 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) []
  b3 = at 3 1 (CS03 ∷ []) (refl) ▸
       at 2 2 [] (lw4 c4 (CS03⁻ ∷ CS03 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸
       at 0 1 (CS03 ∷ []) (refl) ▸
       at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 [] (lw4 c4 (CS03 ∷ CS03⁻ ∷ []) [] tt tt Eq.refl) ▸ done


-- CSu-box-4 @122441: 17 steps
lem-CSu-box-4-at122441 : Complete 4 → ⟪ (CS01 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS01 ∷ []) ⟫ʷ
lem-CSu-box-4-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS01 ∷ Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CS01 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff013 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ CS01 ∷ CS13 ∷ CCZ013 ∷ []) (lw4 c4 (CS01 ∷ Toff013 ∷ []) (Toff013 ∷ CS01 ∷ CS13 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX03 ∷ []) (pw1 c4 (CX03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CX03 ∷ []) (pw1 c4 (CX03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CS01 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff013 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS01 ∷ [])
  b1 = at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 5 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff013 ∷ []) (Toff013 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ CS01 ∷ CS13 ∷ CCZ013 ∷ []) (lw4 c4 (CS01 ∷ Toff013 ∷ []) (Toff013 ∷ CS01 ∷ CS13 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS01 ∷ []) (lw4 c4 (CS01 ∷ CS13 ∷ CCZ013 ∷ CS13 ∷ CZ13 ∷ CCZ013 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS01 ∷ []) (Bx0-2431 ∷ CS01 ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done


-- AX-S23: 8 steps
lem-AX-S23 : Complete 4 → ⟪ (CS01 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS01 ∷ []) ⟫ʷ
lem-AX-S23 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx0-2431 ∷ CS01 ∷ []) (lem-CSu-box-4-at122441 c4) ▸
       at 1 5 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS01 ∷ []) (axAX) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F2-CS0-CS2: 16 steps
lem-F2-CS0-CS2 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F2-CS0-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ CS01 ∷ [])
  b0 = at 0 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (Sb⁻2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (sym (lem-invr-SBOX⟨2·0·41·3⟩ c4)) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (CS01 ∷ []) (lem-F5-01 c4) ▸
       at 3 2 (Sb0-2-43-1 ∷ CS01 ∷ []) (lem-AX-S23 c4) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ []) (sym (lem-inv-SBOX⟨2·0·41·3⟩ c4)) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ CS01 ∷ []) (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ [])
  b1 = at 3 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS0-CS2 c4)) ▸
       at 2 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (lem-invr-SBOX⟨2·0·41·3⟩ c4) ▸
       at 0 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-01 c4)) ▸
       at 3 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 [] (lem-invr-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

