{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D832 where

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
open import Examples.Groups.Clifford+CS.Four.D.D828 using (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CK03-X0)
open import Examples.Groups.Clifford+CS.Four.D.D829 using (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CZ13)
open import Examples.Groups.Clifford+CS.Four.D.D830 using (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CS01 ; lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D831 using (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CX31)
-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [CSd01]: 47 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CSd01 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CSd01 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS01⁻ ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b0 = at 30 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 29 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 28 2 (CS01⁻ ∷ CK32 ∷ []) (sym (low-comm ((CS • CS • CS)) (CK₁₀))) ▸
       at 27 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 26 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 25 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 26 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 25 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸ done

  b1 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS01⁻ ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b1 = at 24 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 25 2 (CS01⁻ ∷ CX02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CX₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 24 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 27 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 25 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 23 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸ done

  b2 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS01⁻ ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS01⁻ ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b2 = at 22 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 21 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 20 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 19 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 18 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 17 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 16 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 15 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸ done

  b3 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS01⁻ ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS01⁻ ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b3 = at 14 2 (CS01⁻ ∷ S3 ∷ []) (sym (low-comm ((CS • CS • CS)) ((S ↑)))) ▸
       at 13 2 (CS01⁻ ∷ CK32 ∷ []) (sym (low-comm ((CS • CS • CS)) (CK₁₀))) ▸
       at 12 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 11 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 10 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 9 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 8 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 7 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸ done

  b4 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS01⁻ ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CX03 ∷ Sw23 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b4 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (CS01⁻ ∷ CX02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CX₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CX03 ∷ Sw23 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b5 = at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CS01⁻ ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (CS01⁻ ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (CS01⁻ ∷ CK02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CK₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (CS01⁻ ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (CS01⁻ ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done


-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [X0 CKd03 X0]: 95 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CKd03-X0 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CKd03-X0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (run b11)))))))))))
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ [])
  b0 = at 34 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 33 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 32 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 34 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 33 2 (Sw01 ∷ CK12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) (Swap • ((S • CK₀₁) ↑)) tt tt Eq.refl) ▸
       at 32 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 33 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 31 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw23 ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ [])
  b1 = at 30 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 29 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 28 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸
       at 27 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 26 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 25 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 24 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b2 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw23 ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ [])
  b2 = at 25 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 24 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 25 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 22 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 21 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 20 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 19 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b3 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ [])
  b3 = at 18 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 17 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 16 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 15 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 14 2 (Sw01 ∷ S3 ∷ []) (sym (low-comm (Swap) ((S ↑)))) ▸
       at 13 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸
       at 12 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 11 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b4 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ [])
  b4 = at 10 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 9 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 8 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 7 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b5 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ [])
  b5 = at 7 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CK12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) (Swap • (CK₀₁ ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 1 34 (X1 ∷ CK13⁻ ∷ X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (win 0 3 complete₃ (CS • CS • CS • CK₀₁ • CS • CS • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CS ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) (X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • CS • CS • CS • CK₀₁ • CS • CS • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CS ↑)) tt tt Eq.refl) ▸ done

  b6 : Chain (Sw01 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ [])
  b6 = at 0 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CK02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S • CK₀₁) ↑)) ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b7 : Chain (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ [])
  b7 = at 4 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CK02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b8 : Chain (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ [])
  b8 = at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 11 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 12 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 13 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 14 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 15 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b9 : Chain (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ [])
  b9 = at 16 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 17 2 (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑))) ▸
       at 18 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 19 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 20 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 21 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 22 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 23 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b10 : Chain (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ [])
  b10 = at 24 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 25 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 26 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 28 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 29 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 27 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b11 = at 28 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 29 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 30 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 31 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 32 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 33 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 34 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- Bar(SSSKSS;0,3->2) passes II/IV units 3 1: 8 steps
lem-Bar⟨SSSKSS03-⟶2⟩-passes-II/IV-units-3-1 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS03-⟶2⟩-passes-II/IV-units-3-1 = run b0
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b0 = at 0 34 (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CK03-X0) ▸
       at 3 32 (CZ13 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CZ13) ▸
       at 4 32 (CS03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CS03) ▸
       at 5 32 (CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CS01) ▸
       at 6 32 (CX31 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CX31) ▸
       at 7 32 (CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CSd01) ▸
       at 8 32 (CX31 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CX31) ▸
       at 9 34 (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CKd03-X0) ▸ done


-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [X0 TOFF301 X0]: 101 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X0 ∷ Sw23 ∷ [])
  b0 = at 34 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 33 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 32 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 33 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 32 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 35 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 33 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 34 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X0 ∷ Sw23 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ X0 ∷ Sw23 ∷ [])
  b1 = at 37 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 35 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 36 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 39 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 37 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 38 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 39 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 40 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ X0 ∷ Sw23 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ X0 ∷ Sw23 ∷ [])
  b2 = at 39 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 38 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 39 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 36 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 35 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 37 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 34 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b3 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ X0 ∷ Sw23 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ Sw23 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS02 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ [])
  b3 = at 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 35 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 32 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 33 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 33 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 31 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 32 3 (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS02 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) (win 3 0 complete₃ (X • Toffᵗ • X) (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (CZ ↑) • (Swap ↑ • CS • Swap ↑) • CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) tt tt Eq.refl) ▸
       at 31 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸ done

  b4 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ Sw23 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS02 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ Sw23 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ [])
  b4 = at 34 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 32 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 33 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 36 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 34 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 37 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 35 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 36 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸ done

  b5 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ Sw23 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X0 ∷ CK03⁻ ∷ Sw23 ∷ X0 ∷ Sw23 ∷ [])
  b5 = at 39 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 37 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 38 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 41 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 39 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 40 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 43 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 41 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X0 ∷ CK03⁻ ∷ Sw23 ∷ X0 ∷ Sw23 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ Sw23 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b6 = at 42 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 43 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 43 (X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (lem-Bar⟨SSSKSS03-⟶2⟩-passes-II/IV-units-3-1) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 10 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸ done

  b7 : Chain (X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ Sw23 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ Sw23 ∷ CS02 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b7 = at 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b8 : Chain (X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ Sw23 ∷ CS02 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (X0 ∷ Sw23 ∷ Toff201 ∷ X0 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b8 = at 3 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 1 12 (X0 ∷ Toff201 ∷ X0 ∷ []) (win 3 0 complete₃ (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (CZ ↑) • (Swap ↑ • CS • Swap ↑) • CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) (X • Toffᵗ • X) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸ done

  b9 : Chain (X0 ∷ Sw23 ∷ Toff201 ∷ X0 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (X0 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K2 ∷ ι ∷ X0 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b9 = at 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b10 : Chain (X0 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K2 ∷ ι ∷ X0 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (X0 ∷ Sw23 ∷ K2 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ X0 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b10 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (K2 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑ ↑)) ((K ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b11 : Chain (X0 ∷ Sw23 ∷ K2 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ X0 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (X0 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X0 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b11 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (K2 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑ ↑)) ((K ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b12 : Chain (X0 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X0 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b12 = at 2 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- Bar(SSSKSS;0,3->2) passes factors of X0 TOFF301 X0: 1 steps
lem-Bar⟨SSSKSS03-⟶2⟩-passes-factors-of-X0-TOFF301-X0 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS03-⟶2⟩-passes-factors-of-X0-TOFF301-X0 = run b0
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  b0 = at 0 34 (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0) ▸ done


-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [X0 CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23 X0]: 159 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (run b19)))))))))))))))))))
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ [])
  b0 = at 62 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 61 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 60 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 59 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 58 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸
       at 57 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 56 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 55 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b1 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ [])
  b1 = at 54 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 56 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 55 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 54 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 55 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 53 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 52 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 51 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b2 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ [])
  b2 = at 50 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 49 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 48 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 47 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 46 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 45 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 44 2 (Sw01 ∷ S3 ∷ []) (sym (low-comm (Swap) ((S ↑)))) ▸
       at 43 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸ done

  b3 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ [])
  b3 = at 42 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 41 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 40 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 39 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 38 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 37 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 36 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 38 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b4 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ [])
  b4 = at 37 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 36 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 37 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 35 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 34 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 33 2 (Sw01 ∷ CK12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) (Swap • (CK₀₁ ↑)) tt tt Eq.refl) ▸
       at 32 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 31 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ [])
  b5 = at 30 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 29 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 28 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸
       at 27 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸
       at 26 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 25 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸
       at 24 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 23 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b6 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ [])
  b6 = at 22 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 23 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 22 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 23 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 20 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 19 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b7 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ [])
  b7 = at 18 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 17 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 16 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 15 2 (Sw01 ∷ S3 ∷ []) (sym (low-comm (Swap) ((S ↑)))) ▸
       at 14 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸
       at 13 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 12 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 11 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b8 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ [])
  b8 = at 10 2 (Sw01 ∷ S3 ∷ []) (sym (low-comm (Swap) ((S ↑)))) ▸
       at 9 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸
       at 8 2 (Sw01 ∷ S3 ∷ []) (sym (low-comm (Swap) ((S ↑)))) ▸
       at 7 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b9 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b9 = at 7 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CK12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) (Swap • (CK₀₁ ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CK12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) (Swap • (CK₀₁ ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CK12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) (Swap • (CK₀₁ ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 1 62 (X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) (win 0 3 complete₃ (CS • CS • CK₀₁ • CS • CK₀₁ • CK₀₁ • (Swap ↑ • CX₀₁ • Swap ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CK₁₀ ↑) • (CK₁₀ ↑) • X • CS • CS • CS • CK₀₁ • CS • CS • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CS ↑) • X) (X • CS • CS • CS • CK₀₁ • CS • CS • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CS ↑) • X • CS • CS • CK₀₁ • CS • CK₀₁ • CK₀₁ • (Swap ↑ • CX₀₁ • Swap ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CK₁₀ ↑) • (CK₁₀ ↑)) tt tt Eq.refl) ▸ done

  b10 : Chain (Sw01 ∷ X1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b10 = at 0 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CK02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b11 = at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 11 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b12 : Chain (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b12 = at 12 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 13 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 14 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 15 2 (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑))) ▸
       at 16 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 17 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 18 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 19 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b13 : Chain (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw23 ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b13 = at 20 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 21 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 22 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 23 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 24 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 26 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b14 : Chain (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw23 ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b14 = at 27 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 25 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 27 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 28 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 29 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 30 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 31 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b15 : Chain (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b15 = at 32 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸
       at 33 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 34 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 35 2 (CK02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 36 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 37 2 (CK02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 38 2 (CK02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 40 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b16 = at 39 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 40 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 41 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 39 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 40 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 41 2 (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑))) ▸
       at 42 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 43 2 (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑))) ▸ done

  b17 : Chain (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b17 = at 44 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 45 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 46 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 47 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 48 2 (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑))) ▸
       at 49 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 50 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 51 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b18 : Chain (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ [])
  b18 = at 52 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 53 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 54 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 56 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 55 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 56 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 57 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 55 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b19 : Chain (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ Sw01 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ Sw01 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ [])
  b19 = at 56 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 57 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 58 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 59 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 60 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 61 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 62 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- Bar(SSKSKK;0,3->2) passes factors of X0 CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23 X0: 1 steps
lem-Bar⟨SSKSKK03-⟶2⟩-passes-factors-of-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK03-⟶2⟩-passes-factors-of-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0 = run b0
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ [])
  b0 = at 0 62 (X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) (lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0) ▸ done

