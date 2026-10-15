{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D810 where

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
open import Examples.Groups.Clifford+CS.Four.D.D807 using (lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-CK03-X0)
open import Examples.Groups.Clifford+CS.Four.D.D808 using (lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CS03 ; lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CZ23)
open import Examples.Groups.Clifford+CS.Four.D.D809 using (lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CS02 ; lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CX32)
-- pass [CS01 CS01 CS01 CK01 CS01 CS01 CX03 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CS13 CK31 CS13 CS13] [CSd02]: 147 steps
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CSd02 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CSd02 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (run b18))))))))))))))))))
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS02⁻ ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ CS13 ∷ [])
  b0 = at 31 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 31 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 32 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 30 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 30 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 30 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸ done

  b1 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b1 = at 31 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 29 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 29 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 (Sw12 ∷ CK32 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 29 2 (CS01⁻ ∷ CK32 ∷ []) (sym (low-comm ((CS • CS • CS)) (CK₁₀))) ▸
       at 30 2 (Sw12 ∷ CK31 ∷ []) (win 0 3 complete₃ ((CK₁₀ ↑) • Swap) (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 28 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 28 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b2 = at 27 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 28 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 29 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 27 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 27 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 27 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 28 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b3 = at 26 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 26 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 26 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 27 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 25 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 26 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 25 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b4 = at 24 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 25 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 24 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 25 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 (CS12⁻ ∷ CX13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CX₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 24 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b5 = at 25 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 26 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 27 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 25 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 24 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 24 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸ done

  b6 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b6 = at 25 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 23 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 23 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 23 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 24 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 22 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 22 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b7 = at 21 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 22 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 23 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 21 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 21 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 21 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 22 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b8 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS23 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b8 = at 20 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 20 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 20 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 21 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 19 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 19 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸ done

  b9 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS23 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS02⁻ ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b9 = at 19 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 20 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 18 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 18 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 18 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 19 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 17 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS02⁻ ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b10 = at 17 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 17 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 18 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 16 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 16 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 16 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸ done

  b11 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS02⁻ ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b11 = at 17 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (CS02⁻ ∷ S3 ∷ []) (sym (low₃-comm ((Swap ↑ • (CS • CS • CS) • Swap ↑)) (S))) ▸
       at 14 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw12 ∷ CK32 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 14 2 (CS01⁻ ∷ CK32 ∷ []) (sym (low-comm ((CS • CS • CS)) (CK₁₀))) ▸
       at 15 2 (Sw12 ∷ CK31 ∷ []) (win 0 3 complete₃ ((CK₁₀ ↑) • Swap) (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS02⁻ ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b12 = at 13 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 13 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 14 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 12 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸ done

  b13 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b13 = at 13 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 11 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 12 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b14 = at 9 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 10 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 11 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 9 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 10 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b15 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b15 = at 8 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 8 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 9 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸ done

  b16 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b16 = at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS12⁻ ∷ CX13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CX₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CS02⁻ ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b17 = at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 5 2 (CS02⁻ ∷ CS01 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) tt tt Eq.refl) ▸
       at 4 2 (CS02⁻ ∷ CS01 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) tt tt Eq.refl) ▸
       at 3 2 (CS02⁻ ∷ CK01 ∷ []) (win 3 0 complete₃ (CK₀₁ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CK₀₁) tt tt Eq.refl) ▸ done

  b18 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CS02⁻ ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS02⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b18 = at 2 2 (CS02⁻ ∷ CS01 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ CS01 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) tt tt Eq.refl) ▸
       at 0 2 (CS02⁻ ∷ CS01 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) tt tt Eq.refl) ▸ done


-- pass [CS01 CS01 CS01 CK01 CS01 CS01 CX03 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CS13 CK31 CS13 CS13] [X0 CKd03 X0]: 121 steps
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-CKd03-X0 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-CKd03-X0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (run b15)))))))))))))))
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ [])
  b0 = at 34 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 33 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 32 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 34 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 31 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 32 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ [])
  b1 = at 31 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ [])
  b2 = at 27 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 24 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ [])
  b3 = at 23 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ [])
  b4 = at 19 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b5 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ [])
  b5 = at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b6 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ Sw23 ∷ CS01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ [])
  b6 = at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 4 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸ done

  b7 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ Sw23 ∷ CS01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ []) (X0 ∷ CK03⁻ ∷ Sw23 ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ [])
  b7 = at 3 2 (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap)) ▸
       at 2 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 1 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 0 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 1 34 (X0 ∷ CK02⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (win 3 0 complete₃ (CS • CS • CS • CK₀₁ • CS • CS • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CS ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) (X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • CS • CS • CS • CK₀₁ • CS • CS • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (X0 ∷ CK03⁻ ∷ Sw23 ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ [])
  b8 = at 2 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 3 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 4 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 5 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 6 2 (CK01 ∷ Sw23 ∷ []) (sym (low-comm (CK₀₁) (Swap))) ▸
       at 7 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b9 : Chain (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ [])
  b9 = at 9 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b10 : Chain (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ [])
  b10 = at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (S3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b11 : Chain (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ [])
  b11 = at 20 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 18 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 21 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 19 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 20 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 23 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 21 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ [])
  b12 = at 24 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 22 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 25 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 23 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 26 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 24 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 27 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 25 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ [])
  b13 = at 28 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 26 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 29 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 27 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 30 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 28 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 31 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 29 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ [])
  b14 = at 32 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 30 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 33 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 31 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 34 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 32 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 35 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 33 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b15 = at 34 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- Bar(SSSKSS;0,3->1) passes II/IV units 3 2: 8 steps
lem-Bar⟨SSSKSS03-⟶1⟩-passes-II/IV-units-3-2 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK03 ∷ X0 ∷ CZ23 ∷ CS03 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ CZ23 ∷ CS03 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS03-⟶1⟩-passes-II/IV-units-3-2 = run b0
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK03 ∷ X0 ∷ CZ23 ∷ CS03 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CZ23 ∷ CS03 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b0 = at 0 34 (X0 ∷ CK03 ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-CK03-X0) ▸
       at 3 32 (CZ23 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CZ23) ▸
       at 4 32 (CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CS03) ▸
       at 5 32 (CS02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CS02) ▸
       at 6 32 (CX32 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CX32) ▸
       at 7 32 (CS02⁻ ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CSd02) ▸
       at 8 32 (CX32 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CX32) ▸
       at 9 34 (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-CKd03-X0) ▸ done


-- pass [CS01 CS01 CS01 CK01 CS01 CS01 CX03 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CS13 CK31 CS13 CS13] [X0 TOFF302 X0]: 117 steps
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-TOFF302-X0 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ Toff302 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff302 ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-TOFF302-X0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ [])
  b0 = at 34 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 33 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 32 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 33 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 32 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 33 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 34 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 35 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b1 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ [])
  b1 = at 36 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 37 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 38 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 39 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 37 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 38 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 39 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸ done

  b2 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K3 ∷ ι1 ∷ X1 ∷ Sw01 ∷ [])
  b2 = at 40 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 39 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 38 2 (Sw01 ∷ K3 ∷ []) (sym (low-comm (Swap) ((K ↑)))) ▸
       at 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 39 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 38 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 37 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 38 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K3 ∷ ι1 ∷ X1 ∷ Sw01 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ X1 ∷ Toff312 ∷ X1 ∷ Sw01 ∷ [])
  b3 = at 36 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 35 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 34 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 33 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 32 2 (Sw01 ∷ K3 ∷ []) (sym (low-comm (Swap) ((K ↑)))) ▸
       at 33 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 33 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 31 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ X1 ∷ Toff312 ∷ X1 ∷ Sw01 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK03 ∷ X0 ∷ Sw01 ∷ CZ23 ∷ CS13 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ [])
  b4 = at 32 3 (X1 ∷ CK13 ∷ X1 ∷ CZ23 ∷ CS13 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (win 0 3 complete₃ (X • Toffᵗ • X) (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (CZ ↑) • (Swap ↑ • CS • Swap ↑) • CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) tt tt Eq.refl) ▸
       at 31 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸
       at 33 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 32 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 33 2 (CK02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 34 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 32 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 33 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸ done

  b5 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK03 ∷ X0 ∷ Sw01 ∷ CZ23 ∷ CS13 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK03 ∷ X0 ∷ CZ23 ∷ CS03 ∷ CS02 ∷ CX32 ∷ Sw01 ∷ CS12⁻ ∷ CX32 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ [])
  b5 = at 34 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 35 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 36 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 37 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 35 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 36 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 37 2 (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀)) ▸ done

  b6 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK03 ∷ X0 ∷ CZ23 ∷ CS03 ∷ CS02 ∷ CX32 ∷ Sw01 ∷ CS12⁻ ∷ CX32 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK03 ∷ X0 ∷ CZ23 ∷ CS03 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ X0 ∷ CK03⁻ ∷ Sw01 ∷ X1 ∷ Sw01 ∷ [])
  b6 = at 38 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 39 2 (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀)) ▸
       at 40 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸
       at 42 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 41 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 42 2 (CK02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S • CK₀₁) ↑)) ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 43 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 41 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK03 ∷ X0 ∷ CZ23 ∷ CS03 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ X0 ∷ CK03⁻ ∷ Sw01 ∷ X1 ∷ Sw01 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CZ23 ∷ CS03 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ X0 ∷ Sw23 ∷ Sw01 ∷ CK12⁻ ∷ Sw23 ∷ X1 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b7 = at 42 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸
       at 43 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 0 43 (X0 ∷ CK03 ∷ X0 ∷ CZ23 ∷ CS03 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (lem-Bar⟨SSSKSS03-⟶1⟩-passes-II/IV-units-3-2) ▸
       at 12 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CK12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) (Swap • ((S • CK₀₁) ↑)) tt tt Eq.refl) ▸ done

  b8 : Chain (X0 ∷ CK03 ∷ X0 ∷ CZ23 ∷ CS03 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ X0 ∷ Sw23 ∷ Sw01 ∷ CK12⁻ ∷ Sw23 ∷ X1 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CZ23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b8 = at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CX32 ∷ []) (sym (low-comm (Swap) (CX₁₀))) ▸
       at 7 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX32 ∷ []) (sym (low-comm (Swap) (CX₁₀))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (X0 ∷ CK03 ∷ X0 ∷ CZ23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (X0 ∷ Sw23 ∷ CK02 ∷ Sw01 ∷ Sw23 ∷ X1 ∷ CZ23 ∷ CS13 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b9 = at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CZ23 ∷ []) (sym (low-comm (Swap) (CZ))) ▸
       at 2 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b10 : Chain (X0 ∷ Sw23 ∷ CK02 ∷ Sw01 ∷ Sw23 ∷ X1 ∷ CZ23 ∷ CS13 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (X0 ∷ K3 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ X1 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b10 = at 2 2 (Sw01 ∷ CK12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) (Swap • (CK₀₁ ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 1 12 (X1 ∷ Toff312 ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (CZ ↑) • (Swap ↑ • CS • Swap ↑) • CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) (X • Toffᵗ • X) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸
       at 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸ done

  b11 : Chain (X0 ∷ K3 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ X1 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (X0 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K3 ∷ ι1 ∷ X1 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b11 = at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b12 : Chain (X0 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K3 ∷ ι1 ∷ X1 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (X0 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ X1 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b12 = at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 8 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 2 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b13 : Chain (X0 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ X1 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (X0 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b13 = at 6 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 9 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸ done

  b14 : Chain (X0 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b14 = at 2 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸
       at 3 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- Bar(SSSKSS;0,3->1) passes factors of X0 TOFF302 X0: 1 steps
lem-Bar⟨SSSKSS03-⟶1⟩-passes-factors-of-X0-TOFF302-X0 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ Toff302 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff302 ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS03-⟶1⟩-passes-factors-of-X0-TOFF302-X0 = run b0
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ [])
  b0 = at 0 34 (X0 ∷ Toff302 ∷ X0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-TOFF302-X0) ▸ done

