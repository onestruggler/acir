{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D142 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0470 ; wl1713 ; wl1714 ; wp0007)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-box-tQ-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D136 using (lem-box-cP-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D141 using (lem-L-CCZ-1-at0440 ; lem-t-cP-at0440)
-- box2 @0440: 11 steps
lem-box2-at0440 : Ws → ⟪ (Bx4-1230 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1230 ∷ Bx4-1230 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  b0 = at 0 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at0440 c4) ▸
       at 4 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at0440 c4) ▸
       at 4 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0470 (lit c4))) ▸
       at 5 5 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff412 ∷ []) (lem-t-cP-at0440 c4) ▸
       at 5 4 (Bx4-1230 ∷ []) (sym (lem-box-cP-at0440 c4)) ▸
       at 5 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at0440 c4) ▸
       at 4 2 [] (wl0470 (lit c4)) ▸
       at 3 2 [] (wp0007 c4) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) []
  b1 = at 2 2 [] (wl0470 (lit c4)) ▸
       at 1 2 [] (wp0007 c4) ▸
       at 0 2 [] (wl0470 (lit c4)) ▸ done


-- ckt-TT @0440: 5 steps
lem-ckt-TT-at0440 : Ws → ⟪ (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-ckt-TT-at0440 c4 = run b0
  where
  b0 : Chain (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) []
  b0 = at 1 45 (Bx4-1230 ∷ []) (lem-L-CCZ-1-at0440 c4) ▸
       at 5 45 (Bx4-1230 ∷ []) (lem-L-CCZ-1-at0440 c4) ▸
       at 2 3 [] (wl1713 (lit c4)) ▸
       at 1 2 [] (lem-box2-at0440 c4) ▸
       at 0 3 [] (wl1714 (lit c4)) ▸ done

