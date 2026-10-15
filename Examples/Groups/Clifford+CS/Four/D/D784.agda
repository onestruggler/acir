{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D784 where

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
open import Examples.Groups.Clifford+CS.Four.D.D783 using (lem-merge-R0-at3012)
-- L87 X3: 230 steps
lem-L87-X3 : ⟪ (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X0 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-L87-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (run b28))))))))))))))))))))))))))))
  where
  b0 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X0 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X0 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ [])
  b0 = at 15 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 16 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 17 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 18 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 15 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 16 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸ done

  b1 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X0 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X0 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ [])
  b1 = at 14 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 24 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 25 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 26 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 27 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 28 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 23 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 24 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

  b2 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X0 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X0 ∷ X0 ∷ X2 ∷ X0 ∷ X3 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ [])
  b2 = at 25 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 26 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸
       at 22 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 23 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 34 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 35 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 36 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 37 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸ done

  b3 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X0 ∷ X0 ∷ X2 ∷ X0 ∷ X3 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ [])
  b3 = at 38 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 39 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 33 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 34 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 35 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 36 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 37 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸
       at 32 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ [])
  b4 = at 32 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 33 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 43 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 44 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 45 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 46 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 47 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 48 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done

  b5 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ [])
  b5 = at 42 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 43 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 44 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸
       at 41 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 42 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 54 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 55 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 56 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

  b6 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ [])
  b6 = at 57 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 58 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 59 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 53 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸
       at 53 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 54 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 55 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸
       at 52 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸ done

  b7 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ [])
  b7 = at 53 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 63 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 64 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 65 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 66 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 67 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 68 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 69 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done

  b8 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X1 ∷ X0 ∷ X3 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ [])
  b8 = at 62 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 63 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸
       at 61 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 62 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 62 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 63 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸
       at 73 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 74 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸ done

  b9 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X1 ∷ X0 ∷ X3 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ [])
  b9 = at 75 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 76 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 77 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 78 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 79 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 80 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 72 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸
       at 71 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸ done

  b10 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X1 ∷ X0 ∷ X3 ∷ [])
  b10 = at 72 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 73 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 74 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸
       at 71 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 72 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 82 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 83 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 84 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸ done

  b11 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ X1 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ X0 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X1 ∷ X0 ∷ X3 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X3 ∷ [])
  b11 = at 81 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 82 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸
       at 80 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 81 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 5 18 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (lem-merge-R0-at3012) ▸
       at 10 18 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (lem-merge-R0-at3012) ▸
       at 16 18 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (lem-merge-R0-at3012) ▸
       at 21 18 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (lem-merge-R0-at3012) ▸ done

  b12 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X3 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b12 = at 26 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 25 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 24 2 (Sw23 ∷ S2⁻ ∷ []) (win 0 3 complete₃ (((S • S • S) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((S • S • S) ↑)) tt tt Eq.refl) ▸
       at 23 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 24 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 26 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 24 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b13 = at 25 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 28 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 26 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 30 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 28 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 30 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b14 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b14 = at 31 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 30 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 29 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 27 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b15 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ Sw23 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b15 = at 25 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 23 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 24 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 24 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 21 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸ done

  b16 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ Sw23 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b16 = at 20 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 19 2 (Sw23 ∷ S2⁻ ∷ []) (win 0 3 complete₃ (((S • S • S) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((S • S • S) ↑)) tt tt Eq.refl) ▸
       at 18 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 21 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 19 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b17 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b17 = at 23 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 21 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 25 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 23 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 25 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 26 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b18 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b18 = at 25 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 24 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 22 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 20 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b19 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b19 = at 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 18 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 19 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 19 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 16 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 15 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b20 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b20 = at 14 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 13 2 (Sw23 ∷ S2⁻ ∷ []) (win 0 3 complete₃ (((S • S • S) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((S • S • S) ↑)) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b21 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b21 = at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 17 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 19 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 20 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b22 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b22 = at 19 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 18 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 16 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b23 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ X0 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ Sw23 ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b23 = at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 13 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 13 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 9 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸ done

  b24 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ Sw23 ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b24 = at 8 2 (Sw23 ∷ S2⁻ ∷ []) (win 0 3 complete₃ (((S • S • S) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((S • S • S) ↑)) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b25 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ Sw23 ∷ ι ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b25 = at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b26 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ Sw23 ∷ ι ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b26 = at 13 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ CS01⁻ ∷ S3 ∷ K3 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (S3 ∷ S3 ∷ X0 ∷ Sw23 ∷ X1 ∷ X2 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ [])
  b27 = at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 8 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 8 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 4 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b28 : Chain (S3 ∷ S3 ∷ X0 ∷ Sw23 ∷ X1 ∷ X2 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ [])
  b28 = at 2 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 1 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 1 26 (X2 ∷ []) (win 3 0 complete₃ ((S ↑ ↑) • (S ↑ ↑) • X • (X ↑) • (X ↑ ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (X ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

