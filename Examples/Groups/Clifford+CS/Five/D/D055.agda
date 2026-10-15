{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D055 where

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
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D031 using (lem-box-perm-1324-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-box-cP-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D052 using (lem-box-perm-3241-at243243 ; lem-box-perm-4213-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CX14-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-comm-CCZ024-CS13 ; lem-comm-CCZ024-CSd13 ; lem-comm-TOFF014-CX23)
-- F4-CS2-CS1: 254 steps
lem-F4-CS2-CS1 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-CS1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (run b31)))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (pw2 c4 (X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (lw4 c4 (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Sb0-2-43-1 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 10 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 7 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CZ01 ∷ []) (pw2 c4 (CZ01 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (pw2 c4 (X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CCZ014 ∷ CS12⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (lw2 c4 (X4 ∷ CZ01 ∷ CZ01 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CCZ014 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CCZ014 ∷ CS12⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff023 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 6 2 (Toff023 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff023 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) (pw2 c4 (Toff134 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ034 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff023 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 11 2 (Toff023 ∷ K1⁻ ∷ []) (lw4 c4 (K1⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 8 2 (Toff023 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 6 2 (Toff023 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ Toff023 ∷ []) (Toff023 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff023 ∷ K1 ∷ []) (lw4 c4 (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ014 ∷ CCZ034 ∷ CCZ234 ∷ Toff023 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b5 = at 8 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CCZ014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 10 2 (CCZ014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 8 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 9 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ014 ∷ CCZ034 ∷ CCZ234 ∷ Toff023 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b6 = at 6 2 (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) (pw2 c4 (Toff134 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (Toff134 ∷ []) (pw2 c4 (Toff134 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff023 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 13 2 (Toff023 ∷ K1⁻ ∷ []) (lw4 c4 (K1⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Toff023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 10 2 (Toff023 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ014 ∷ CS12 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b7 = at 9 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 8 2 (Toff023 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ Toff023 ∷ []) (Toff023 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff023 ∷ K1 ∷ []) (lw4 c4 (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 8 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 3 2 (CCZ014 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS12 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ014 ∷ CS12 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff023 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b8 = at 4 2 (Toff023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 2 (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) (pw2 c4 (Toff134 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ034 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff023 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b9 = at 9 2 (Toff023 ∷ K1⁻ ∷ []) (lw4 c4 (K1⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 6 2 (Toff023 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 4 2 (Toff023 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ Toff023 ∷ []) (Toff023 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ K1 ∷ []) (lw4 c4 (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 4 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ014 ∷ CCZ034 ∷ CCZ234 ∷ Toff023 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b10 = at 6 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 8 2 (CCZ014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 6 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ014 ∷ CCZ034 ∷ CCZ234 ∷ Toff023 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b11 = at 4 2 (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) (pw2 c4 (Toff134 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff134 ∷ []) (pw2 c4 (Toff134 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff023 ∷ K1⁻ ∷ []) (lw4 c4 (K1⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 8 2 (Toff023 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b12 = at 7 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 c4) ▸
       at 6 2 (Toff023 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ Toff023 ∷ []) (Toff023 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff023 ∷ K1 ∷ []) (lw4 c4 (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-box-perm-4213-at122441 c4) ▸
       at 2 1 (Bx0-2431 ∷ []) (lem-box-perm-3241-at243243 c4) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸ done

  b13 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b13 = at 0 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (pw2 c4 (X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (lw4 c4 (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ123 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b14 = at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CZ01 ∷ []) (pw2 c4 (CZ01 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (pw2 c4 (X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (X4 ∷ []) (lw2 c4 (X4 ∷ CZ01 ∷ CZ01 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b15 : Chain (Bx0-1423 ∷ X4 ∷ CCZ123 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ024 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b15 = at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 4 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 3 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b16 : Chain (Bx0-1423 ∷ X4 ∷ CCZ024 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b16 = at 3 2 (Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (Bx0-1423 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b17 = at 5 2 (Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 8 (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 4 3 (CS12 ∷ Toff134 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CS12 ∷ Toff134 ∷ []) (CS12 ∷ Toff134 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b18 : Chain (Bx0-1423 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX23 ∷ Toff324 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b18 = at 2 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸
       at 6 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 6 (CX23 ∷ Toff324 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 2 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸ done

  b19 : Chain (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX23 ∷ Toff324 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b19 = at 5 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 c4) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K3 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ K3 ∷ []) (K3 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS34 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ CS34 ∷ []) (CS34 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 c4) ▸
       at 9 2 (CS34⁻ ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 c4) ▸
       at 11 2 (CS24 ∷ Toff014 ∷ []) (pw3 c4 (Toff014 ∷ CS24 ∷ []) (CS24 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸ done

  b20 : Chain (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ CS34 ∷ CX23 ∷ Toff014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b20 = at 12 2 (K3⁻ ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 c4) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K3 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ K3 ∷ []) (K3 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS34 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ CS34 ∷ []) (CS34 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 c4) ▸ done

  b21 : Chain (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ CS34 ∷ CX23 ∷ Toff014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b21 = at 7 2 (CS34⁻ ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 c4) ▸
       at 9 2 (CS24 ∷ Toff014 ∷ []) (pw3 c4 (Toff014 ∷ CS24 ∷ []) (CS24 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (K3⁻ ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 4 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CZ02 ∷ CCZ124 ∷ Toff014 ∷ []) (pw3 c4 (Toff014 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ124 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (pw3 c4 (Toff014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CZ02 ∷ CCZ024 ∷ []) (pw3 c4 (CZ02 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) (CZ02 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b22 : Chain (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Sb0-2-43-1 ∷ CS13 ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b22 = at 2 5 (CX23 ∷ Toff324 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ []) (CX23 ∷ Toff324 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 4 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ []) (CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b23 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Sb0-2-43-1 ∷ CS13 ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CCZ024 ∷ CS13 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b23 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 5 (CS13 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS13 ∷ []) (CS13 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (CS13 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS13 ∷ []) (CS13 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 c4) ▸
       at 4 2 (CS13 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS13 ∷ []) (CS13 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸ done

  b24 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CCZ024 ∷ CS13 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ [])
  b24 = at 3 2 (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 c4) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ []) (CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX23 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b25 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ Toff014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b25 = at 6 1 (CS12 ∷ []) (refl) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 6 (CX23 ∷ Toff324 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 4 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 7 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (K3 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ K3 ∷ []) (K3 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸ done

  b26 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ Toff014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b26 = at 9 2 (CS34 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ CS34 ∷ []) (CS34 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 c4) ▸
       at 11 2 (CS34⁻ ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 c4) ▸
       at 13 2 (CS24 ∷ Toff014 ∷ []) (pw3 c4 (Toff014 ∷ CS24 ∷ []) (CS24 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (K3⁻ ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 8 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b27 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b27 = at 5 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 c4) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K3 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ K3 ∷ []) (K3 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS34 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ CS34 ∷ []) (CS34 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 c4) ▸
       at 9 2 (CS34⁻ ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 c4) ▸
       at 11 2 (CS24 ∷ Toff014 ∷ []) (pw3 c4 (Toff014 ∷ CS24 ∷ []) (CS24 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸ done

  b28 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ Toff324 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b28 = at 12 2 (K3⁻ ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CZ02 ∷ CCZ124 ∷ Toff014 ∷ []) (pw3 c4 (Toff014 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ124 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (pw3 c4 (Toff014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CZ02 ∷ CCZ024 ∷ []) (pw3 c4 (CZ02 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) (CZ02 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 5 (CX23 ∷ Toff324 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ []) (CX23 ∷ Toff324 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 6 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸ done

  b29 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ Toff324 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS13⁻ ∷ X4 ∷ [])
  b29 = at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 3 (Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX23 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸ done

  b30 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS13⁻ ∷ X4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b30 = at 6 5 (CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 8 2 (CS13⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 c4) ▸
       at 6 2 (CS13⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 c4) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b31 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b31 = at 10 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

