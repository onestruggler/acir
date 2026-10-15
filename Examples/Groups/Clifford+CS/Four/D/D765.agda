{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D765 where

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
open import Examples.Groups.Clifford+CS.Four.D.D763 using (lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1)
open import Examples.Groups.Clifford+CS.Four.D.D764 using (lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 ; lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 ; lem-pass-TOFF312-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1)
-- pass [CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK30 CS02 CS02 CS02 S2 CK20 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S2 S2 S2 S2 CK20 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS01 CS01 CS01 S1 CK10 CS01 CS01 CS01 CS01 CS01 CS01 S3 CK30] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 7 steps
lem-pass-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = run b0
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ [])
  b0 = at 0 80 (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl))) ▸
       at 62 35 (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1) ▸
       at 61 7 (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ Toff312 ∷ []) (lem-pass-TOFF312-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1) ▸
       at 30 37 (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1) ▸
       at 29 7 (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ Toff312 ∷ []) (lem-pass-TOFF312-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1) ▸
       at 0 35 (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1) ▸
       at 6 91 (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (sym (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))) ▸ done


-- groups [CKd30] [CS13 CS23 CX12 CSd23 CX12]: 59 steps
lem-groups-CKd30-vs-CS13-CS23-CX12-CSd23-CX12 : ⟪ (CK30⁻ ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-groups-CKd30-vs-CS13-CS23-CX12-CSd23-CX12 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CK30⁻ ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (CS12 ∷ CK20⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (CS13 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ [])
  b2 = at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23 ∷ CK31⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b3 : Chain (CS13 ∷ CS23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ CS23⁻ ∷ CX12 ∷ [])
  b3 = at 2 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁)) ▸
       at 3 2 (CX13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b4 : Chain (CS13 ∷ CS23 ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ CS23⁻ ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ Sw23 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ [])
  b4 = at 3 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 5 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 3 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (CS13 ∷ CS23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ Sw23 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX12 ∷ [])
  b5 = at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ CK31⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b6 : Chain (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX12 ∷ []) (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b6 = at 4 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁)) ▸
       at 5 2 (CX13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b7 : Chain (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CK30⁻ ∷ [])
  b7 = at 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 5 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- pass [CKd30] [CCZ123]: 3 steps
lem-pass-CKd30-vs-CCZ123 : ⟪ (CK30⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-pass-CKd30-vs-CCZ123 = run b0
  where
  b0 : Chain (CK30⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CK30⁻ ∷ [])
  b0 = at 1 1 (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ []) (win 0 3 complete₃ (CCZ) ((Swap ↑ • CS • Swap ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁) tt tt Eq.refl) ▸
       at 0 6 (CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CK30⁻ ∷ []) (lem-groups-CKd30-vs-CS13-CS23-CX12-CSd23-CX12) ▸
       at 0 5 (CCZ123 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁) (CCZ) tt tt Eq.refl) ▸ done


-- groups [CKd30] [CSd23]: 15 steps
lem-groups-CKd30-vs-CSd23 : ⟪ (CK30⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CK30⁻ ∷ []) ⟫ʷ
lem-groups-CKd30-vs-CSd23 = trans (run b0) (run b1)
  where
  b0 : Chain (CK30⁻ ∷ CS23⁻ ∷ []) (Sw01 ∷ CS23⁻ ∷ CK31⁻ ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ CK31⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ CS23⁻ ∷ CK31⁻ ∷ Sw01 ∷ []) (CS23⁻ ∷ CK30⁻ ∷ [])
  b1 = at 0 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 2 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CKd30] [CSd23]: 1 steps
lem-pass-CKd30-vs-CSd23 : ⟪ (CK30⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CK30⁻ ∷ []) ⟫ʷ
lem-pass-CKd30-vs-CSd23 = run b0
  where
  b0 : Chain (CK30⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK30⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ CK30⁻ ∷ []) (lem-groups-CKd30-vs-CSd23) ▸ done


-- groups [CK10 CS02 CK20 CSd02 CKd10 CS02 CKd20 CSd02] [CS12 CS13 CX23 CSd13 CX23]: 305 steps
lem-groups-CK10-CS02-CK20-CSd02-CKd10-CS02-CKd20-CSd02-vs-CS12-CS13-CX23-CSd13-CX23 : ⟪ (CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-groups-CK10-CS02-CK20-CSd02-CKd10-CS02-CKd20-CSd02-vs-CS12-CS13-CX23-CSd13-CX23 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (run b38))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b0 = at 0 9 (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS ↑)) ((CS ↑) • CK₁₀ • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸ done

  b1 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS13 ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b1 = at 11 2 (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS)) ▸
       at 10 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS13 ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS23 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b2 = at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (CS23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CS)) ▸ done

  b3 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS23 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b3 = at 9 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 5 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b4 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 8 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b5 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b5 = at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b6 = at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap)) ▸
       at 6 2 (CS12 ∷ CK10⁻ ∷ []) (win 3 0 complete₃ ((S ↑ • CK₁₀) • (CS ↑)) ((CS ↑) • (S ↑ • CK₁₀)) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b7 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS)) ▸
       at 6 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b8 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b8 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b9 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b9 = at 4 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS)) ▸
       at 5 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (CS12 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ Sw23 ∷ CS03 ∷ CS12 ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b10 = at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 5 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (CS12 ∷ CK10 ∷ Sw23 ∷ CS03 ∷ CS12 ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CK10 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b11 = at 3 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 4 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b12 : Chain (CS12 ∷ CK10 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ Sw23 ∷ CK10 ∷ CS12 ∷ Sw23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b12 = at 4 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸ done

  b13 : Chain (CS12 ∷ Sw23 ∷ CK10 ∷ CS12 ∷ Sw23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw01 ∷ CS12⁻ ∷ CX23 ∷ Sw01 ∷ CS13⁻ ∷ CX23 ∷ [])
  b13 = at 2 2 (CS12 ∷ CK10 ∷ []) (win 3 0 complete₃ (CK₁₀ • (CS ↑)) ((CS ↑) • CK₁₀) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 9 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸ done

  b14 : Chain (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw01 ∷ CS12⁻ ∷ CX23 ∷ Sw01 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw01 ∷ CX23 ∷ CK21⁻ ∷ Sw01 ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ [])
  b14 = at 10 2 (CX23 ∷ CS12⁻ ∷ []) (win 0 3 complete₃ ((CS • CS • CS) • (CX₀₁ ↑)) ((CX₀₁ ↑) • (CS • CS • CS)) tt tt Eq.refl) ▸
       at 9 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 10 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 10 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 8 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 9 2 (CX23 ∷ CK21⁻ ∷ []) (win 0 3 complete₃ ((S ↑ • CK₁₀) • (CX₀₁ ↑)) ((CX₀₁ ↑) • (S ↑ • CK₁₀)) tt tt Eq.refl) ▸ done

  b15 : Chain (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw01 ∷ CX23 ∷ CK21⁻ ∷ Sw01 ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CX23 ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ [])
  b15 = at 8 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 9 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 7 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 8 2 (CX23 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (CX₀₁ ↑)) ((CX₀₁ ↑) • CS) tt tt Eq.refl) ▸
       at 7 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸ done

  b16 : Chain (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CX23 ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CX23 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ [])
  b16 = at 8 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁)) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 5 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 6 2 (CX23 ∷ CS12⁻ ∷ []) (win 0 3 complete₃ ((CS • CS • CS) • (CX₀₁ ↑)) ((CX₀₁ ↑) • (CS • CS • CS)) tt tt Eq.refl) ▸
       at 5 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸ done

  b17 : Chain (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CX23 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CX23 ∷ CK20 ∷ Sw01 ∷ Sw01 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ [])
  b17 = at 6 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 4 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 5 2 (CX23 ∷ CK21 ∷ []) (win 0 3 complete₃ (CK₁₀ • (CX₀₁ ↑)) ((CX₀₁ ↑) • CK₁₀) tt tt Eq.refl) ▸
       at 4 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 5 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b18 : Chain (CS12 ∷ CS13 ∷ CK10 ∷ CS02 ∷ CX23 ∷ CK20 ∷ Sw01 ∷ Sw01 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CK10 ∷ CX23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ [])
  b18 = at 6 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 3 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (CX23 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (CX₀₁ ↑)) ((CX₀₁ ↑) • CS) tt tt Eq.refl) ▸
       at 3 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b19 : Chain (CS12 ∷ CS13 ∷ CK10 ∷ CX23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ [])
  b19 = at 2 2 (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁)) ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸ done

  b20 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS13⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b20 = at 13 2 (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS))) ▸
       at 12 2 (CS13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS13⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CX23 ∷ [])
  b21 = at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 12 2 (CS23⁻ ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) ((CS • CS • CS))) ▸ done

  b22 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b22 = at 11 2 (CS13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 5 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b23 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 10 2 (CS13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b24 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b24 = at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b25 = at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap)) ▸
       at 8 2 (CS12⁻ ∷ CK10⁻ ∷ []) (win 3 0 complete₃ ((S ↑ • CK₁₀) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (S ↑ • CK₁₀)) tt tt Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b26 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b26 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS))) ▸
       at 8 2 (CS13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b27 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b27 = at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b28 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b28 = at 6 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS))) ▸
       at 7 2 (CS13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b29 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ Sw23 ∷ CS03 ∷ CS12⁻ ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b29 = at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 5 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ Sw23 ∷ CS03 ∷ CS12⁻ ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b30 = at 5 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 6 2 (CS13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b31 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CK10 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ Sw23 ∷ CK10 ∷ CS12⁻ ∷ Sw23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ [])
  b31 = at 6 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸ done

  b32 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ Sw23 ∷ CK10 ∷ CS12⁻ ∷ Sw23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw01 ∷ CS12⁻ ∷ CX23 ∷ Sw01 ∷ [])
  b32 = at 4 2 (CS12⁻ ∷ CK10 ∷ []) (win 3 0 complete₃ (CK₁₀ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CK₁₀) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 12 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 11 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸ done

  b33 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ Sw01 ∷ CS12⁻ ∷ CX23 ∷ Sw01 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw01 ∷ CX23 ∷ CK21⁻ ∷ Sw01 ∷ CS02⁻ ∷ [])
  b33 = at 12 2 (CX23 ∷ CS12⁻ ∷ []) (win 0 3 complete₃ ((CS • CS • CS) • (CX₀₁ ↑)) ((CX₀₁ ↑) • (CS • CS • CS)) tt tt Eq.refl) ▸
       at 11 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 12 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 12 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 10 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 11 2 (CX23 ∷ CK21⁻ ∷ []) (win 0 3 complete₃ ((S ↑ • CK₁₀) • (CX₀₁ ↑)) ((CX₀₁ ↑) • (S ↑ • CK₁₀)) tt tt Eq.refl) ▸ done

  b34 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ Sw01 ∷ CX23 ∷ CK21⁻ ∷ Sw01 ∷ CS02⁻ ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CX23 ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CK20⁻ ∷ CS02⁻ ∷ [])
  b34 = at 10 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 11 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 10 2 (CX23 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (CX₀₁ ↑)) ((CX₀₁ ↑) • CS) tt tt Eq.refl) ▸
       at 9 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸ done

  b35 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CX23 ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CX23 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ [])
  b35 = at 10 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 8 2 (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁)) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 7 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 8 2 (CX23 ∷ CS12⁻ ∷ []) (win 0 3 complete₃ ((CS • CS • CS) • (CX₀₁ ↑)) ((CX₀₁ ↑) • (CS • CS • CS)) tt tt Eq.refl) ▸
       at 7 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸ done

  b36 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CK20 ∷ CX23 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CX23 ∷ CK20 ∷ Sw01 ∷ Sw01 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ [])
  b36 = at 8 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 6 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 7 2 (CX23 ∷ CK21 ∷ []) (win 0 3 complete₃ (CK₁₀ • (CX₀₁ ↑)) ((CX₀₁ ↑) • CK₁₀) tt tt Eq.refl) ▸
       at 6 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 7 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b37 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CS02 ∷ CX23 ∷ CK20 ∷ Sw01 ∷ Sw01 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CX23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ [])
  b37 = at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 6 2 (CX23 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (CX₀₁ ↑)) ((CX₀₁ ↑) • CS) tt tt Eq.refl) ▸
       at 5 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b38 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CK10 ∷ CX23 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ [])
  b38 = at 4 2 (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁)) ▸ done


-- pass [CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S2 S2 S2 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02] [CCZ123]: 5 steps
lem-pass-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-vs-CCZ123 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-vs-CCZ123 = run b0
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ [])
  b0 = at 56 1 (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (win 0 3 complete₃ (CCZ) (CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 0 56 (CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (S ↑ ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 0 13 (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (lem-groups-CK10-CS02-CK20-CSd02-CKd10-CS02-CKd20-CSd02-vs-CS12-CS13-CX23-CSd13-CX23) ▸
       at 5 8 (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (win 3 0 complete₃ (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (S ↑ ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 0 5 (CCZ123 ∷ []) (win 0 3 complete₃ (CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑)) (CCZ) tt tt Eq.refl) ▸ done

