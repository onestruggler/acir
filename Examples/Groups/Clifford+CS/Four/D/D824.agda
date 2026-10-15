{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D824 where

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
open import Examples.Groups.Clifford+CS.Four.D.D823 using (lem-Bar⟨SSSKSS03-⟶2⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶2⟩)
-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [X0 CS02 CS02 CK02 CS02 CK02 CK02 CX01 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX01 CS12 CS12 CK12 CS12 CK12 CK12 X0]: 3 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 = run b0
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b0 = at 31 31 (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX01 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (win 3 0 complete₃ (X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • CX₀₁ • (CK₀₁ ↑) • (S ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CK₀₁ ↑) • (CK₀₁ ↑) • X) (X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • CX₀₁ • X • (CK₀₁ ↑) • (S ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • X • CX₀₁ • X • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CK₀₁ ↑) • (CK₀₁ ↑)) tt tt Eq.refl) ▸
       at 0 66 (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX01 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (lem-Bar⟨SSSKSS03-⟶2⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶2⟩) ▸
       at 0 35 (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) (win 3 0 complete₃ (X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • CX₀₁ • X • (CK₀₁ ↑) • (S ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • X • CX₀₁ • X • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CK₀₁ ↑) • (CK₀₁ ↑)) (X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • CX₀₁ • (CK₀₁ ↑) • (S ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CK₀₁ ↑) • (CK₀₁ ↑) • X) tt tt Eq.refl) ▸ done


-- Bar(SSSKSS;0,3->2) passes factors of X0 CS02 CS02 CK02 CS02 CK02 CK02 CX01 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX01 CS12 CS12 CK12 CS12 CK12 CK12 X0: 1 steps
lem-Bar⟨SSSKSS03-⟶2⟩-passes-factors-of-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS03-⟶2⟩-passes-factors-of-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 = run b0
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b0 = at 0 62 (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0) ▸ done


-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [X0 CK03 X0]: 91 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CK03-X0 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CK03-X0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (run b11)))))))))))
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw01 ∷ [])
  b0 = at 32 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 31 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 30 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 32 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 31 2 (Sw01 ∷ CK12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) (Swap • (CK₀₁ ↑)) tt tt Eq.refl) ▸
       at 30 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 31 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw23 ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw01 ∷ [])
  b1 = at 28 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸
       at 27 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸
       at 26 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 25 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸
       at 24 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 23 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 22 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b2 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw23 ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw01 ∷ [])
  b2 = at 23 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 22 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 23 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 20 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 19 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 18 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 17 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b3 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ Sw01 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw01 ∷ [])
  b3 = at 16 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 15 2 (Sw01 ∷ S3 ∷ []) (sym (low-comm (Swap) ((S ↑)))) ▸
       at 14 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸
       at 13 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 12 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 11 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 10 2 (Sw01 ∷ S3 ∷ []) (sym (low-comm (Swap) ((S ↑)))) ▸
       at 9 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸ done

  b4 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ Sw01 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ Sw01 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw01 ∷ [])
  b4 = at 8 2 (Sw01 ∷ S3 ∷ []) (sym (low-comm (Swap) ((S ↑)))) ▸
       at 7 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CK12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) (Swap • (CK₀₁ ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ Sw01 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw01 ∷ []) (X0 ∷ Sw01 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b5 = at 4 2 (Sw01 ∷ CK12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) (Swap • (CK₀₁ ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CK12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) (Swap • (CK₀₁ ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 1 32 (X1 ∷ CK13 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) (win 0 3 complete₃ (CS • CS • CK₀₁ • CS • CK₀₁ • CK₀₁ • (Swap ↑ • CX₀₁ • Swap ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CK₁₀ ↑) • (CK₁₀ ↑) • X • (Swap ↑ • CK₀₁ • Swap ↑) • X) (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • CS • CS • CK₀₁ • CS • CK₀₁ • CK₀₁ • (Swap ↑ • CX₀₁ • Swap ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CK₁₀ ↑) • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (X0 ∷ Sw01 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ Sw01 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b6 = at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CK02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CK02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b7 : Chain (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ Sw01 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ Sw01 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b7 = at 6 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CK02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (CK02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ Sw01 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ Sw01 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b8 = at 10 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 11 2 (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑))) ▸
       at 12 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 13 2 (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑))) ▸
       at 14 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 15 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 16 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 17 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸ done

  b9 : Chain (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ Sw01 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b9 = at 18 2 (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑))) ▸
       at 19 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 20 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 21 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 22 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 23 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 24 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ Sw01 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b10 = at 25 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 26 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 27 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 25 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 27 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 28 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 29 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b11 : Chain (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ Sw01 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ [])
  b11 = at 30 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 31 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 32 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

