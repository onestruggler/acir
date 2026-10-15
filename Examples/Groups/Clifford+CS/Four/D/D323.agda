{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D323 where

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

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CS23 X2]: 137 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS23-X2 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS23-X2 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (run b17)))))))))))))))))
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS23 ∷ CK10 ∷ X2 ∷ CS01 ∷ CS01 ∷ [])
  b0 = at 30 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 31 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 32 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 29 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 30 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 31 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 28 2 (X2 ∷ CK10 ∷ []) (low-comm (CK₁₀) (X)) ▸
       at 29 2 (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS)) ▸ done

  b1 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS23 ∷ CK10 ∷ X2 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS23 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b1 = at 30 2 (X2 ∷ CK10 ∷ []) (low-comm (CK₁₀) (X)) ▸
       at 27 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 28 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 29 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 26 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 27 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 28 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 25 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸ done

  b2 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS23 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS23 ∷ CS01 ∷ X2 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b2 = at 26 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 27 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 24 4 (X2 ∷ CS23 ∷ X2 ∷ CX21 ∷ []) (win 0 3 complete₃ (CX₁₀ • (X ↑) • (CS ↑) • (X ↑)) ((X ↑) • (CS ↑) • (X ↑) • CX₁₀) tt tt Eq.refl) ▸
       at 23 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 24 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 25 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 22 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 23 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸ done

  b3 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS23 ∷ CS01 ∷ X2 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS01 ∷ CS23 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b3 = at 24 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 21 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 22 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 23 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 20 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 21 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 22 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 19 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸ done

  b4 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS01 ∷ CS23 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS23 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b4 = at 20 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 21 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 18 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 19 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 20 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 17 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 18 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 19 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸ done

  b5 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS23 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ X2 ∷ CS23 ∷ S1 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b5 = at 16 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 17 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 18 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 15 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 16 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 17 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 14 2 (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X)) ▸
       at 15 2 (CS23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CS)) ▸ done

  b6 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ X2 ∷ CS23 ∷ S1 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS01 ∷ CS23 ∷ X2 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b6 = at 16 2 (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X)) ▸
       at 13 2 (X2 ∷ CK10 ∷ []) (low-comm (CK₁₀) (X)) ▸
       at 14 2 (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS)) ▸
       at 15 2 (X2 ∷ CK10 ∷ []) (low-comm (CK₁₀) (X)) ▸
       at 12 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 13 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 14 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 11 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸ done

  b7 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS01 ∷ CS23 ∷ X2 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS23 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b7 = at 12 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 13 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 10 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 11 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 12 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 9 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 10 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 11 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸ done

  b8 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS23 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS23 ∷ X2 ∷ Sw01 ∷ Sw01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b8 = at 8 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 9 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 10 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 7 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 8 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 9 2 (X2 ∷ CS01 ∷ []) (low-comm (CS) (X)) ▸
       at 6 4 (X2 ∷ CS23 ∷ X2 ∷ CX21 ∷ []) (win 0 3 complete₃ (CX₁₀ • (X ↑) • (CS ↑) • (X ↑)) ((X ↑) • (CS ↑) • (X ↑) • CX₁₀) tt tt Eq.refl) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b9 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS23 ∷ X2 ∷ Sw01 ∷ Sw01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ X2 ∷ CS23 ∷ X2 ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b9 = at 8 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 7 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 6 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 6 4 (X2 ∷ CS23 ∷ X2 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (X ↑) • (CS ↑) • (X ↑)) ((X ↑) • (CS ↑) • (X ↑) • CS) tt tt Eq.refl) ▸
       at 5 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b10 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ X2 ∷ CS23 ∷ X2 ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ Sw01 ∷ X2 ∷ CS23 ∷ X2 ∷ CS12 ∷ Sw01 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b10 = at 8 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 6 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 4 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 5 4 (X2 ∷ CS23 ∷ X2 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (X ↑) • (CS ↑) • (X ↑)) ((X ↑) • (CS ↑) • (X ↑) • CS) tt tt Eq.refl) ▸ done

  b11 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ Sw01 ∷ X2 ∷ CS23 ∷ X2 ∷ CS12 ∷ Sw01 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ X2 ∷ Sw01 ∷ CS23 ∷ X2 ∷ Sw01 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b11 = at 4 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b12 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ X2 ∷ Sw01 ∷ CS23 ∷ X2 ∷ Sw01 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS23 ∷ X2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b12 = at 4 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 3 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 4 4 (X2 ∷ CS23 ∷ X2 ∷ CK21 ∷ []) (win 0 3 complete₃ (CK₁₀ • (X ↑) • (CS ↑) • (X ↑)) ((X ↑) • (CS ↑) • (X ↑) • CK₁₀) tt tt Eq.refl) ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 6 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b13 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS23 ∷ X2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ CS02 ∷ X2 ∷ CS23 ∷ Sw01 ∷ X2 ∷ CS12 ∷ Sw01 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b13 = at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 3 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 2 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 3 4 (X2 ∷ CS23 ∷ X2 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (X ↑) • (CS ↑) • (X ↑)) ((X ↑) • (CS ↑) • (X ↑) • CS) tt tt Eq.refl) ▸
       at 2 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b14 : Chain (CS02 ∷ CS02 ∷ X2 ∷ CS23 ∷ Sw01 ∷ X2 ∷ CS12 ∷ Sw01 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ Sw01 ∷ CS12 ∷ X2 ∷ CS23 ∷ X2 ∷ Sw01 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b14 = at 4 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 3 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸ done

  b15 : Chain (CS02 ∷ Sw01 ∷ CS12 ∷ X2 ∷ CS23 ∷ X2 ∷ Sw01 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (CS02 ∷ X2 ∷ CS23 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b15 = at 2 4 (X2 ∷ CS23 ∷ X2 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (X ↑) • (CS ↑) • (X ↑)) ((X ↑) • (CS ↑) • (X ↑) • CS) tt tt Eq.refl) ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸ done

  b16 : Chain (CS02 ∷ X2 ∷ CS23 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CS23 ∷ X2 ∷ CS02 ∷ Sw01 ∷ Sw01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b16 = at 2 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 0 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 1 4 (X2 ∷ CS23 ∷ X2 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (X ↑) • (CS ↑) • (X ↑)) ((X ↑) • (CS ↑) • (X ↑) • CS) tt tt Eq.refl) ▸
       at 0 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b17 : Chain (X2 ∷ CS23 ∷ X2 ∷ CS02 ∷ Sw01 ∷ Sw01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CS23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b17 = at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

