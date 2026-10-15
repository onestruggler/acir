{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D095 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.Windows using (win)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain

-- sw0 CK21: 2 steps
lem-sw0-CK21 : ⟪ (Sw01 ∷ CK21 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ []) ⟫ʷ
lem-sw0-CK21 = run b0
  where
  b0 : Chain (Sw01 ∷ CK21 ∷ Sw01 ∷ []) (CK20 ∷ [])
  b0 = at 0 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CKd21: 2 steps
lem-sw0-CKd21 : ⟪ (Sw01 ∷ CK21⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ []) ⟫ʷ
lem-sw0-CKd21 = run b0
  where
  b0 : Chain (Sw01 ∷ CK21⁻ ∷ Sw01 ∷ []) (CK20⁻ ∷ [])
  b0 = at 0 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CS23: 2 steps
lem-sw0-CS23 : ⟪ (Sw01 ∷ CS23 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-sw0-CS23 = run b0
  where
  b0 : Chain (Sw01 ∷ CS23 ∷ Sw01 ∷ []) (CS23 ∷ [])
  b0 = at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CSd23: 2 steps
lem-sw0-CSd23 : ⟪ (Sw01 ∷ CS23⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ []) ⟫ʷ
lem-sw0-CSd23 = run b0
  where
  b0 : Chain (Sw01 ∷ CS23⁻ ∷ Sw01 ∷ []) (CS23⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CZ23: 2 steps
lem-sw0-CZ23 : ⟪ (Sw01 ∷ CZ23 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ []) ⟫ʷ
lem-sw0-CZ23 = run b0
  where
  b0 : Chain (Sw01 ∷ CZ23 ∷ Sw01 ∷ []) (CZ23 ∷ [])
  b0 = at 0 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CX23: 2 steps
lem-sw0-CX23 : ⟪ (Sw01 ∷ CX23 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
lem-sw0-CX23 = run b0
  where
  b0 : Chain (Sw01 ∷ CX23 ∷ Sw01 ∷ []) (CX23 ∷ [])
  b0 = at 0 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CK23: 2 steps
lem-sw0-CK23 : ⟪ (Sw01 ∷ CK23 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ []) ⟫ʷ
lem-sw0-CK23 = run b0
  where
  b0 : Chain (Sw01 ∷ CK23 ∷ Sw01 ∷ []) (CK23 ∷ [])
  b0 = at 0 2 (CK23 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₀₁)) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CKd23: 2 steps
lem-sw0-CKd23 : ⟪ (Sw01 ∷ CK23⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ []) ⟫ʷ
lem-sw0-CKd23 = run b0
  where
  b0 : Chain (Sw01 ∷ CK23⁻ ∷ Sw01 ∷ []) (CK23⁻ ∷ [])
  b0 = at 0 2 (CK23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • CK₀₁))) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CX30: 6 steps
lem-sw0-CX30 : ⟪ (Sw01 ∷ CX30 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
lem-sw0-CX30 = run b0
  where
  b0 : Chain (Sw01 ∷ CX30 ∷ Sw01 ∷ []) (CX31 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CX21 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) ((CX₁₀ ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CK30: 6 steps
lem-sw0-CK30 : ⟪ (Sw01 ∷ CK30 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ []) ⟫ʷ
lem-sw0-CK30 = run b0
  where
  b0 : Chain (Sw01 ∷ CK30 ∷ Sw01 ∷ []) (CK31 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK21 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) ((CK₁₀ ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CKd30: 6 steps
lem-sw0-CKd30 : ⟪ (Sw01 ∷ CK30⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ []) ⟫ʷ
lem-sw0-CKd30 = run b0
  where
  b0 : Chain (Sw01 ∷ CK30⁻ ∷ Sw01 ∷ []) (CK31⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK21⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (((S ↑ • CK₁₀) ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CX31: 6 steps
lem-sw0-CX31 : ⟪ (Sw01 ∷ CX31 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
lem-sw0-CX31 = run b0
  where
  b0 : Chain (Sw01 ∷ CX31 ∷ Sw01 ∷ []) (CX30 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CK31: 6 steps
lem-sw0-CK31 : ⟪ (Sw01 ∷ CK31 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ []) ⟫ʷ
lem-sw0-CK31 = run b0
  where
  b0 : Chain (Sw01 ∷ CK31 ∷ Sw01 ∷ []) (CK30 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CKd31: 6 steps
lem-sw0-CKd31 : ⟪ (Sw01 ∷ CK31⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK30⁻ ∷ []) ⟫ʷ
lem-sw0-CKd31 = run b0
  where
  b0 : Chain (Sw01 ∷ CK31⁻ ∷ Sw01 ∷ []) (CK30⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CX32: 2 steps
lem-sw0-CX32 : ⟪ (Sw01 ∷ CX32 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
lem-sw0-CX32 = run b0
  where
  b0 : Chain (Sw01 ∷ CX32 ∷ Sw01 ∷ []) (CX32 ∷ [])
  b0 = at 0 2 (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀)) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CK32: 2 steps
lem-sw0-CK32 : ⟪ (Sw01 ∷ CK32 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ []) ⟫ʷ
lem-sw0-CK32 = run b0
  where
  b0 : Chain (Sw01 ∷ CK32 ∷ Sw01 ∷ []) (CK32 ∷ [])
  b0 = at 0 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

