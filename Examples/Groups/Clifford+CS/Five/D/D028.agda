{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D028 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0181 ; wl0207 ; wl0464 ; wl0729 ; wl1172 ; wl1173 ; wp0312 ; wp0313 ; wp0314 ; wp0979 ; wp0980 ; wp0981 ; wp0982)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym-ab-at03122031)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-sym-bc-at031031)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-Xb-box-at243243 ; lem-box-perm-1324-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-perm-1324-at3443 ; lem-pairs-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ034-CX12)

-- CKc-box @3443: 61 steps
lem-CKc-box-at3443 : Ws → ⟪ (Bx0-1243 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-1243 ∷ []) ⟫ʷ
lem-CKc-box-at3443 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx0-1243 ∷ CK43 ∷ []) (X4 ∷ Bx0-1243 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b0 = at 1 0 (CCZ123 ∷ CCZ123 ∷ []) (sym (wl0181 (lit c4))) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-box-perm-1324-at3443 c4) ▸
       at 0 2 (X4 ∷ Bx0-1423 ∷ X4 ∷ []) (sym (lem-Xb-box-at243243 c4)) ▸
       at 3 2 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ123 ∷ []) (sym (wl1172 (lit c4))) ▸
       at 2 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 3 2 (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (sym (wl0729 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸ done

  b1 : Chain (X4 ∷ Bx0-1243 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b1 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 4 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸
       at 5 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 6 2 (CS23⁻ ∷ CCZ034 ∷ []) (wp0313 c4) ▸
       at 7 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 8 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ034 ∷ CS13 ∷ X4 ∷ CCZ123 ∷ [])
  b2 = at 5 2 (K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp0979 c4) ▸
       at 8 2 (CZ03 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ []) (wp0980 c4) ▸
       at 11 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 13 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 12 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸
       at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS23⁻ ∷ CCZ034 ∷ []) (wp0313 c4) ▸
       at 15 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ034 ∷ CS13 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ034 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ [])
  b3 = at 16 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸
       at 12 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 7 (K3 ∷ CK43 ∷ S4 ∷ []) (sym (wp0982 c4)) ▸
       at 3 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸
       at 4 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 5 2 (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀)) ▸
       at 6 2 (S4 ∷ Toff012 ∷ []) (c₃ (Toff) (S ↑)) ▸
       at 7 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff012 ∷ CCZ034 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ [])
  b4 = at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 2 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸
       at 3 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 4 2 (CS23⁻ ∷ CCZ034 ∷ []) (wp0313 c4) ▸
       at 5 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 6 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp0979 c4) ▸ done

  b5 : Chain (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ [])
  b5 = at 6 2 (CZ03 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ []) (wp0980 c4) ▸
       at 9 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 11 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 10 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸
       at 11 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 12 2 (CS23⁻ ∷ CCZ034 ∷ []) (wp0313 c4) ▸
       at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸ done

  b6 : Chain (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Bx0-1243 ∷ X4 ∷ CCZ123 ∷ [])
  b6 = at 10 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 7 (K3 ∷ CK43 ∷ S4 ∷ []) (sym (wp0982 c4)) ▸
       at 1 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸
       at 2 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 3 2 (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀)) ▸
       at 4 2 (S4 ∷ Toff012 ∷ []) (c₃ (Toff) (S ↑)) ▸
       at 5 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸
       at 6 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Bx0-1243 ∷ X4 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-1243 ∷ [])
  b7 = at 6 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 0 6 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl1173 (lit c4))) ▸
       at 3 3 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-Xb-box-at243243 c4) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸
       at 3 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸ done

-- box-perm-4132 @03243240: 3 steps
lem-box-perm-4132-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-4132-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-2014 ∷ []) (lem-pairs-at03243240 c4) ▸
       at 0 1 (Bx3-0214 ∷ []) (lem-sym-ab-at03122031 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-bc-at031031 c4) ▸ done
