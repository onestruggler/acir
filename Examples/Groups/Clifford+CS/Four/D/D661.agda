{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D661 where

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
open import Examples.Groups.Clifford+CS.Four.D.D236 using (lem-AXIOM-LF-at0231)
open import Examples.Groups.Clifford+CS.Four.D.D337 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK20-X2 ; lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd20-X2)
open import Examples.Groups.Clifford+CS.Four.D.D608 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D609 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D614 using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D615 using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D636 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd02-X2)
open import Examples.Groups.Clifford+CS.Four.D.D637 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS02-X2)
open import Examples.Groups.Clifford+CS.Four.D.D638 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-TOFF102-X0-X2)
open import Examples.Groups.Clifford+CS.Four.D.D641 using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-TOFF102-X0-X2)
open import Examples.Groups.Clifford+CS.Four.D.D648 using (lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D650 using (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Z1-CZ12-CZ13-CCZ123 ; lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D658 using (lem-b2g-1011PP0 ; lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2 ; lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 ; lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D659 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D660 using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3 ; lem-pass-CSd30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 ; lem-pass-TOFF123-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3 ; lem-pass-X3-CS30-X3-vs-X2-TOFF012-CS03-TOFF012-CSd03-X2)
-- pass [CS30] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 25 steps
lem-pass-CS30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (CS03 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CS03 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b0 = at 1 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Sw23 ∷ X2 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 9 (X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-X2-TOFF012-CS03-TOFF012-CSd03-X2) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (X3 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Sw23 ∷ X2 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ [])
  b2 = at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 8 4 (X2 ∷ CS02 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b3 : Chain (X3 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ [])
  b3 = at 0 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 236 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (run b29)))))))))))))))))))))))))))))
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ Sw01 ∷ Sw23 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b0 = at 29 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 29 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 28 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 29 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b1 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ Sw01 ∷ Sw23 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ Sw01 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b1 = at 28 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 27 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 28 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 27 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 26 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 27 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ Sw01 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b2 = at 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 26 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 25 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 26 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 25 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b3 = at 24 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 25 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 24 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 23 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 24 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸ done

  b4 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b4 = at 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 22 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 21 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 22 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 21 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b5 = at 20 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 21 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 20 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 19 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 20 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b6 = at 20 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 19 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 18 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 19 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 18 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 17 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b7 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b7 = at 18 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 17 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 16 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 17 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw01 ∷ S3 ∷ []) (sym (low-comm (Swap) ((S ↑)))) ▸
       at 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b8 = at 16 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 15 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 14 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 15 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b9 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b9 = at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 13 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b10 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ Sw01 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b10 = at 12 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ S3 ∷ []) (sym (low-comm (Swap) ((S ↑)))) ▸
       at 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b11 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ Sw01 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw01 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b11 = at 10 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ S3 ∷ []) (sym (low-comm (Swap) ((S ↑)))) ▸
       at 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸ done

  b12 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw01 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CK20 ∷ Sw01 ∷ CS13 ∷ CK21⁻ ∷ CS13⁻ ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b12 = at 5 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 1 29 (CK21 ∷ CS13 ∷ CK21⁻ ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b13 : Chain (CK20 ∷ Sw01 ∷ CS13 ∷ CK21⁻ ∷ CS13⁻ ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CK20 ∷ CS03 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b13 = at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b14 : Chain (CK20 ∷ CS03 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ CS03 ∷ CK20⁻ ∷ CS03⁻ ∷ [])
  b14 = at 4 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 3 9 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03⁻ ∷ []) (lem-pass-CSd30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 2 9 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20⁻ ∷ []) (lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 1 9 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ []) (lem-pass-CS30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 0 9 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ []) (lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸ done

  b15 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ CS03 ∷ CK20⁻ ∷ CS03⁻ ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ CS13⁻ ∷ Sw01 ∷ [])
  b15 = at 12 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ CS13⁻ ∷ Sw01 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ [])
  b16 = at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 9 4 (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (win 0 3 complete₃ (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b17 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ Sw23 ∷ CK20 ∷ Sw01 ∷ Sw23 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ [])
  b17 = at 10 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 16 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b18 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ Sw23 ∷ CK20 ∷ Sw01 ∷ Sw23 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ Sw01 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ [])
  b18 = at 17 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 15 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑))) ▸
       at 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 18 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 19 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 17 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸ done

  b19 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ Sw01 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ [])
  b19 = at 18 2 (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑))) ▸
       at 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 20 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 21 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 19 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b20 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ [])
  b20 = at 21 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 22 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 20 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 22 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 23 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 21 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ [])
  b21 = at 23 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 23 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 24 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 22 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑))) ▸
       at 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b22 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ [])
  b22 = at 25 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 26 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 24 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 26 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 27 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 25 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ [])
  b23 = at 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 27 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 28 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 26 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 28 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b24 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ [])
  b24 = at 29 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 27 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 29 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 30 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 28 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ [])
  b25 = at 29 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 30 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 31 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 29 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 31 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 32 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b26 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ [])
  b26 = at 33 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 31 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 32 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 33 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 34 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 32 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 34 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ CS13 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ [])
  b27 = at 33 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 34 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 35 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 33 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 34 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 35 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 36 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b28 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CK31 ∷ CK31 ∷ Sw01 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ Sw01 ∷ CK21 ∷ Sw23 ∷ Sw01 ∷ [])
  b28 = at 34 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 36 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 35 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 36 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 37 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 35 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 37 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 36 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b29 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ Sw01 ∷ CK21 ∷ Sw23 ∷ Sw01 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  b29 = at 37 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 38 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 36 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 37 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- Bar(SSKSKK;2,3->0) passes split Gad(t=0, W=(2, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ = trans (run b0) (run b1)
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b0 = at 0 32 (X2 ∷ CK20 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK20-X2) ▸
       at 3 32 (X2 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS02-X2) ▸
       at 6 32 (X2 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS02-X2) ▸
       at 9 32 (X2 ∷ CK20⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd20-X2) ▸
       at 12 37 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 20 32 (X2 ∷ CK20 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK20-X2) ▸
       at 23 32 (X2 ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd02-X2) ▸
       at 26 32 (X2 ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd02-X2) ▸ done

  b1 : Chain (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  b1 = at 29 32 (X2 ∷ CK20⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd20-X2) ▸ done


-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 X3 K0 S0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 Sd0 Kd0 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3 = run b0
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  b0 = at 29 16 (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2) ▸
       at 0 61 (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩) ▸
       at 0 32 (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ []) (sym lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2) ▸ done


-- far CS02 CS02 CK20 CS02 CX23 CS03 CS03 CS03 .. 1011PP0 sep 2: 9 steps
lem-far-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03-··-1011PP0-sep-2 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ X0 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ []) ⟫ʷ
lem-far-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03-··-1011PP0-sep-2 = trans (run b0) (run b1)
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ X0 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ [])
  b0 = at 80 10 (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ []) (lem-b2g-1011PP0) ▸
       at 0 80 (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Toff123 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ Toff123 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-AXIOM-LF-at0231) ▸
       at 62 45 (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3) ▸
       at 61 17 (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ Toff123 ∷ []) (lem-pass-TOFF123-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3) ▸
       at 30 47 (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3) ▸
       at 29 17 (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ Toff123 ∷ []) (lem-pass-TOFF123-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3) ▸
       at 0 45 (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3) ▸
       at 16 91 (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ []) (sym lem-AXIOM-LF-at0231) ▸ done

  b1 : Chain (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ [])
  b1 = at 0 16 (X0 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (sym lem-b2g-1011PP0) ▸ done


-- distribute Gad(t=1, W=(0, 2, 3), d=1, e=1) TOFF102 CS13 TOFF102 CSd13: 25 steps
lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X2 ∷ X0 ∷ X3 ∷ CS13 ∷ X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 4 0 (X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑) • (X ↑ ↑) • X • (X ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 11 0 (X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑) • (X ↑ ↑) • X • (X ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 18 0 (X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑) • (X ↑ ↑) • X • (X ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ X3 ∷ []) (sym (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))) ▸
       at 3 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 4 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 5 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸ done

  b1 : Chain (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X2 ∷ X0 ∷ X3 ∷ CS13 ∷ X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X3 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b1 = at 6 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 7 2 (CS13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CS • Swap ↑))) ▸
       at 8 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 5 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 6 2 (CS13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (Toff102 ∷ X3 ∷ []) (sym (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))) ▸
       at 11 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸ done

  b2 : Chain (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X3 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X2 ∷ X2 ∷ X3 ∷ [])
  b2 = at 12 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 13 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 14 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 15 2 (CS13⁻ ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 16 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 13 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 14 2 (CS13⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X2 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  b3 = at 15 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 30 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X2 ∷ X0 ∷ X3 ∷ CS13 ∷ X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 33 0 (X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑) • (X ↑ ↑) • X • (X ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 40 0 (X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑) • (X ↑ ↑) • X • (X ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 47 0 (X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑) • (X ↑ ↑) • X • (X ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 31 2 (Toff102 ∷ X3 ∷ []) (sym (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))) ▸
       at 32 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 33 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 34 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 34 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸ done

  b1 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X2 ∷ X0 ∷ X3 ∷ CS13 ∷ X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X3 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b1 = at 35 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 36 2 (CS13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CS • Swap ↑))) ▸
       at 37 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 34 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 35 2 (CS13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 36 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 39 2 (Toff102 ∷ X3 ∷ []) (sym (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))) ▸
       at 40 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸ done

  b2 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X3 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X2 ∷ X2 ∷ X3 ∷ [])
  b2 = at 41 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 42 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 42 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 43 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 44 2 (CS13⁻ ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 45 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 42 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 43 2 (CS13⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X2 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  b3 = at 44 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 0 34 (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-TOFF102-X0-X2) ▸
       at 5 32 (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3) ▸
       at 8 34 (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-TOFF102-X0-X2) ▸
       at 13 32 (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3) ▸
       at 0 16 (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (sym lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13) ▸ done


-- pass [X2 CKd23 X2] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 9 steps
lem-pass-X2-CKd23-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ CK23⁻ ∷ X2 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X0 ∷ X3 ∷ [])
  b0 = at 0 5 (X0 ∷ X3 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (win 1 2 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • X • (X ↑ ↑)) (X • (X ↑ ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 15 (X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 14 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ []) (lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 11 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK23 ∷ X2 ∷ []) (lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 8 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 5 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK23 ∷ X2 ∷ []) (lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 2 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ []) (lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 15 (X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  b1 = at 6 17 (X0 ∷ X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (win 1 2 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • X • (X ↑ ↑)) (X • (X ↑ ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CKd23] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 7 steps
lem-pass-CKd23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (CK23⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK23⁻ ∷ []) ⟫ʷ
lem-pass-CKd23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = run b0
  where
  b0 : Chain (CK23⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK23⁻ ∷ [])
  b0 = at 1 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 0 2 (X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (win 0 3 complete₃ (((S • CK₀₁) ↑) • (X ↑)) ((X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 11 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 11 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3) ▸
       at 9 4 (X2 ∷ CK23⁻ ∷ []) (win 0 3 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑)) ((X ↑) • ((S • CK₀₁) ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 8 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3] [CCZ123]: 28 steps
lem-pass-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3-vs-CCZ123 : ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3-vs-CCZ123 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 9 2 (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • CCZ) (CZ • CCZ • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 10 2 (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CCZ) ((Swap ↑ • CZ • Swap ↑) • CCZ • (X ↑)) tt tt Eq.refl) ▸
       at 7 2 (Z1 ∷ X0 ∷ []) (low₁-comm (X) (Z)) ▸
       at 8 2 (CZ12 ∷ X0 ∷ []) (low₁-comm (X) (CZ)) ▸
       at 9 2 (CZ13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CZ • Swap ↑))) ▸
       at 10 2 (CCZ123 ∷ X0 ∷ []) (low₁-comm (X) (CCZ)) ▸
       at 3 8 (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Z1-CZ12-CZ13-CCZ123) ▸ done

  b1 : Chain (X0 ∷ X2 ∷ X3 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ Z1 ∷ Z1 ∷ CZ12 ∷ Z1 ∷ CZ13 ∷ X2 ∷ CZ12 ∷ CCZ123 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b1 = at 2 2 (Z1 ∷ X3 ∷ []) (sym (low-comm ((Z ↑)) ((X ↑)))) ▸
       at 3 2 (CZ12 ∷ X3 ∷ []) (sym (low₃-comm ((CZ ↑)) (X))) ▸
       at 4 2 (Z1 ∷ CZ13 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CZ • Swap ↑)) (Z • (Swap ↑ • CZ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 6 2 (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • CCZ) (CZ • CCZ • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 2 (Z1 ∷ X2 ∷ []) (sym (low-comm ((Z ↑)) (X))) ▸
       at 2 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 4 2 (Z1 ∷ X2 ∷ []) (sym (low-comm ((Z ↑)) (X))) ▸
       at 5 2 (CZ13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (X0 ∷ Z1 ∷ Z1 ∷ CZ12 ∷ Z1 ∷ CZ13 ∷ X2 ∷ CZ12 ∷ CCZ123 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (Z1 ∷ Z1 ∷ CZ12 ∷ Z1 ∷ CZ13 ∷ Z1 ∷ X0 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b2 = at 6 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 2 (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CCZ) ((Swap ↑ • CZ • Swap ↑) • CCZ • (X ↑)) tt tt Eq.refl) ▸
       at 0 2 (Z1 ∷ X0 ∷ []) (low₁-comm (X) (Z)) ▸
       at 1 2 (Z1 ∷ X0 ∷ []) (low₁-comm (X) (Z)) ▸
       at 2 2 (CZ12 ∷ X0 ∷ []) (low₁-comm (X) (CZ)) ▸
       at 3 2 (Z1 ∷ X0 ∷ []) (low₁-comm (X) (Z)) ▸
       at 4 2 (CZ13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CZ • Swap ↑))) ▸
       at 5 2 (Z1 ∷ X0 ∷ []) (low₁-comm (X) (Z)) ▸ done

  b3 : Chain (Z1 ∷ Z1 ∷ CZ12 ∷ Z1 ∷ CZ13 ∷ Z1 ∷ X0 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b3 = at 6 2 (CZ12 ∷ X0 ∷ []) (low₁-comm (X) (CZ)) ▸
       at 7 2 (CZ13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CZ • Swap ↑))) ▸
       at 8 2 (CCZ123 ∷ X0 ∷ []) (low₁-comm (X) (CCZ)) ▸
       at 0 9 (CCZ123 ∷ []) (win 0 3 complete₃ (Z • Z • CZ • Z • (Swap ↑ • CZ • Swap ↑) • Z • CZ • (Swap ↑ • CZ • Swap ↑) • CCZ) (CCZ) tt tt Eq.refl) ▸ done


-- pass [CCZ123] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 1 steps
lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 11 (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (sym lem-pass-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3-vs-CCZ123) ▸ done


-- CCZ(2,1,3) passes split Gad(t=1, W=(0, 2, 3), d=1, e=1): 1 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡1⟩ : ⟪ (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡1⟩ = run b0
  where
  b0 : Chain (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 11 (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3) ▸ done


-- pass [X2 CK23 X2] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 9 steps
lem-pass-X2-CK23-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK23-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ CK23 ∷ X2 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X0 ∷ X3 ∷ [])
  b0 = at 0 5 (X0 ∷ X3 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (win 1 2 complete₃ ((X ↑) • (CK₀₁ ↑) • (X ↑) • X • (X ↑ ↑)) (X • (X ↑ ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 15 (X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 14 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 11 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 8 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ []) (lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 5 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 2 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 15 (X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK23 ∷ X2 ∷ [])
  b1 = at 6 17 (X0 ∷ X3 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (win 1 2 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • X • (X ↑ ↑)) (X • (X ↑ ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CK23] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 7 steps
lem-pass-CK23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (CK23 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK23 ∷ []) ⟫ʷ
lem-pass-CK23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = run b0
  where
  b0 : Chain (CK23 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK23 ∷ [])
  b0 = at 1 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 0 2 (X2 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (win 0 3 complete₃ ((CK₀₁ ↑) • (X ↑)) ((X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 11 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 11 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (lem-pass-X2-CK23-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3) ▸
       at 9 4 (X2 ∷ CK23 ∷ []) (win 0 3 complete₃ ((X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑)) ((X ↑) • (CK₀₁ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 8 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [TOFF312] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 5 steps
lem-pass-TOFF312-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (Toff312 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff312 ∷ []) ⟫ʷ
lem-pass-TOFF312-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = run b0
  where
  b0 : Chain (Toff312 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff312 ∷ [])
  b0 = at 0 1 (CK23 ∷ CCZ123 ∷ CK23⁻ ∷ []) (win 0 3 complete₃ (Toffᵗ) ((CK₀₁ ↑) • CCZ • ((S • CK₀₁) ↑)) tt tt Eq.refl) ▸
       at 2 11 (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK23⁻ ∷ []) (lem-pass-CKd23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3) ▸
       at 1 11 (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3) ▸
       at 0 11 (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK23 ∷ []) (lem-pass-CK23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3) ▸
       at 10 3 (Toff312 ∷ []) (win 0 3 complete₃ ((CK₀₁ ↑) • CCZ • ((S • CK₀₁) ↑)) (Toffᵗ) tt tt Eq.refl) ▸ done


-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 30 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X2 ∷ X0 ∷ X3 ∷ CS13 ∷ X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 35 0 (X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑) • (X ↑ ↑) • X • (X ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 42 0 (X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑) • (X ↑ ↑) • X • (X ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 49 0 (X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑) • (X ↑ ↑) • X • (X ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 33 2 (Toff102 ∷ X3 ∷ []) (sym (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))) ▸
       at 34 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 35 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 36 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 36 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸ done

  b1 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X2 ∷ X0 ∷ X3 ∷ CS13 ∷ X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X3 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b1 = at 37 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 38 2 (CS13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CS • Swap ↑))) ▸
       at 39 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 36 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 37 2 (CS13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 38 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 41 2 (Toff102 ∷ X3 ∷ []) (sym (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))) ▸
       at 42 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸ done

  b2 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X3 ∷ X2 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X2 ∷ X2 ∷ X3 ∷ [])
  b2 = at 43 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 44 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 44 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 45 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 46 2 (CS13⁻ ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 47 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 44 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 45 2 (CS13⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X2 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  b3 = at 46 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 0 36 (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-TOFF102-X0-X2) ▸
       at 5 34 (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3) ▸
       at 8 36 (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-TOFF102-X0-X2) ▸
       at 13 34 (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3) ▸
       at 0 16 (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (sym lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13) ▸ done

