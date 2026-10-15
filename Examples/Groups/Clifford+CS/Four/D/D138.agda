{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D138 where

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
open import Examples.Groups.Clifford+CS.Four.D.D041 using (lem-S2-at0213-ᵖ-1)
open import Examples.Groups.Clifford+CS.Four.D.D124 using (lem-pass-X3-CSd32-X3-vs-CS01 ; lem-pass-X3-CSd32-X3-vs-CSd01 ; lem-pass-X3-CSd32-X3-vs-TOFF023)
open import Examples.Groups.Clifford+CS.Four.D.D125 using (lem-pass-CS23-vs-CSd03 ; lem-pass-CS23-vs-S0 ; lem-pass-CS23-vs-TOFF012 ; lem-pass-X3-CKd32-X3-vs-CS01 ; lem-pass-X3-CKd32-X3-vs-CSd01 ; lem-pass-X3-CKd32-X3-vs-TOFF023 ; lem-pass-X3-CS32-X3-vs-CS01 ; lem-pass-X3-CS32-X3-vs-CSd01 ; lem-pass-X3-CS32-X3-vs-TOFF023)
open import Examples.Groups.Clifford+CS.Four.D.D126 using (lem-pass-CS23-vs-CS03 ; lem-pass-CS23-vs-Sd0)
open import Examples.Groups.Clifford+CS.Four.D.D137 using (lem-pass-CKd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 ; lem-pass-CS32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 ; lem-pass-X3-CSd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0)
-- pass [CSd32] [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3]: 5 steps
lem-pass-CSd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : ⟪ (CS23⁻ ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-CSd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = run b0
  where
  b0 : Chain (CS23⁻ ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23⁻ ∷ [])
  b0 = at 1 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 0 2 (X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 9 (X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0) ▸
       at 7 4 (X3 ∷ CS23⁻ ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸ done


-- ca-split Gad(t=2, W=(0, 3), d=SdKdSS, e=-1) 3: 23 steps
lem-ca-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩-3 : ⟪ (X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩-3 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ [])
  b0 = at 1 2 (S2⁻ ∷ X3 ∷ []) (sym (low₃-comm (((S • S • S) ↑ ↑)) (X))) ▸
       at 0 2 (S2⁻ ∷ X0 ∷ []) (low₁-comm (X) (((S • S • S) ↑))) ▸
       at 2 2 (K2⁻ ∷ X3 ∷ []) (sym (low₃-comm (((K • iI) ↑ ↑)) (X))) ▸
       at 1 2 (K2⁻ ∷ X0 ∷ []) (low₁-comm (X) (((K • iI) ↑))) ▸
       at 3 2 (S2 ∷ X3 ∷ []) (sym (low₃-comm ((S ↑ ↑)) (X))) ▸
       at 2 2 (S2 ∷ X0 ∷ []) (low₁-comm (X) ((S ↑))) ▸
       at 4 2 (S2 ∷ X3 ∷ []) (sym (low₃-comm ((S ↑ ↑)) (X))) ▸
       at 3 2 (S2 ∷ X0 ∷ []) (low₁-comm (X) ((S ↑))) ▸ done

  b1 : Chain (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ [])
  b1 = at 13 2 (X0 ∷ S2 ∷ []) (sym (low₁-comm (X) ((S ↑)))) ▸
       at 12 2 (X0 ∷ K2 ∷ []) (sym (low₁-comm (X) ((K ↑)))) ▸
       at 11 2 (X0 ∷ S2⁻ ∷ []) (sym (low₁-comm (X) (((S • S • S) ↑)))) ▸
       at 10 2 (X0 ∷ S2⁻ ∷ []) (sym (low₁-comm (X) (((S • S • S) ↑)))) ▸
       at 14 2 (X3 ∷ S2 ∷ []) (low₃-comm ((S ↑ ↑)) (X)) ▸
       at 13 2 (X3 ∷ K2 ∷ []) (low₃-comm ((K ↑ ↑)) (X)) ▸
       at 12 2 (X3 ∷ S2⁻ ∷ []) (low₃-comm (((S • S • S) ↑ ↑)) (X)) ▸
       at 11 2 (X3 ∷ S2⁻ ∷ []) (low₃-comm (((S • S • S) ↑ ↑)) (X)) ▸ done

  b2 : Chain (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b2 = at 0 4 (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ []) (win 0 3 complete₃ (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 24 4 (CS23⁻ ∷ CS23⁻ ∷ CK32 ∷ CS23 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (win 0 3 complete₃ (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 15 9 (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23 ∷ []) (lem-pass-CS32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3) ▸
       at 14 9 (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23 ∷ []) (lem-pass-CS32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3) ▸
       at 13 9 (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CK32⁻ ∷ []) (lem-pass-CKd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3) ▸
       at 12 9 (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23⁻ ∷ []) (lem-pass-CSd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3) ▸
       at 20 8 [] (win 0 3 complete₃ (((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [X3 CSd32 X3] [CS01 TOFF023 CSd01 TOFF023]: 4 steps
lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = run b0
  where
  b0 : Chain (X3 ∷ CS23⁻ ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  b0 = at 0 4 (CS01 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-CS01) ▸
       at 1 4 (Toff023 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-TOFF023) ▸
       at 2 4 (CS01⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-CSd01) ▸
       at 3 4 (Toff023 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-TOFF023) ▸ done


-- pass [X3 CSd32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (lem-S2-at0213-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023) ▸
       at 0 4 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-S2-at0213-ᵖ-1) ▸ done


-- pass [X3 CKd32 X3] [CS01 TOFF023 CSd01 TOFF023]: 4 steps
lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = run b0
  where
  b0 : Chain (X3 ∷ CK32⁻ ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  b0 = at 0 4 (CS01 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-CS01) ▸
       at 1 4 (Toff023 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-TOFF023) ▸
       at 2 4 (CS01⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-CSd01) ▸
       at 3 4 (Toff023 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-TOFF023) ▸ done


-- pass [X3 CKd32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CKd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (X3 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (lem-S2-at0213-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023) ▸
       at 0 4 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-S2-at0213-ᵖ-1) ▸ done


-- pass [X3 CS32 X3] [CS01 TOFF023 CSd01 TOFF023]: 4 steps
lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = run b0
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b0 = at 0 4 (CS01 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CS01) ▸
       at 1 4 (Toff023 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-TOFF023) ▸
       at 2 4 (CS01⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CSd01) ▸
       at 3 4 (Toff023 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-TOFF023) ▸ done


-- pass [X3 CS32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (lem-S2-at0213-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023) ▸
       at 0 4 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-S2-at0213-ᵖ-1) ▸ done


-- pass [CS23] [iI]: 1 steps
lem-pass-CS23-vs-iI : ⟪ (CS23 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-iI = run b0
  where
  b0 : Chain (CS23 ∷ ι ∷ []) (ι ∷ CS23 ∷ [])
  b0 = at 0 2 (ι ∷ CS23 ∷ []) (win 1 2 complete₃ ((CS ↑) • iI) (iI • (CS ↑)) tt tt Eq.refl) ▸ done


-- pass [CS23] [Sd3]: 1 steps
lem-pass-CS23-vs-Sd3 : ⟪ (CS23 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-Sd3 = run b0
  where
  b0 : Chain (CS23 ∷ S3⁻ ∷ []) (S3⁻ ∷ CS23 ∷ [])
  b0 = at 0 2 (S3⁻ ∷ CS23 ∷ []) (win 0 3 complete₃ ((CS ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑ ↑) • (CS ↑)) tt tt Eq.refl) ▸ done


-- pass [CS23] [S3]: 1 steps
lem-pass-CS23-vs-S3 : ⟪ (CS23 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-S3 = run b0
  where
  b0 : Chain (CS23 ∷ S3 ∷ []) (S3 ∷ CS23 ∷ [])
  b0 = at 0 2 (S3 ∷ CS23 ∷ []) (win 0 3 complete₃ ((CS ↑) • (S ↑ ↑)) ((S ↑ ↑) • (CS ↑)) tt tt Eq.refl) ▸ done


-- pass [CS23] [iI Sd0 Sd3 CS03 TOFF012 iI iI iI S0 S3 CSd03 TOFF012]: 12 steps
lem-pass-CS23-vs-iI-Sd0-Sd3-CS03-TOFF012-iI-iI-iI-S0-S3-CSd03-TOFF012 : ⟪ (CS23 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-iI-Sd0-Sd3-CS03-TOFF012-iI-iI-iI-S0-S3-CSd03-TOFF012 = trans (run b0) (run b1)
  where
  b0 : Chain (CS23 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ CS23 ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 0 2 (ι ∷ CS23 ∷ []) (lem-pass-CS23-vs-iI) ▸
       at 1 2 (S0⁻ ∷ CS23 ∷ []) (lem-pass-CS23-vs-Sd0) ▸
       at 2 2 (S3⁻ ∷ CS23 ∷ []) (lem-pass-CS23-vs-Sd3) ▸
       at 3 2 (CS03 ∷ CS23 ∷ []) (lem-pass-CS23-vs-CS03) ▸
       at 4 2 (Toff012 ∷ CS23 ∷ []) (lem-pass-CS23-vs-TOFF012) ▸
       at 5 2 (ι ∷ CS23 ∷ []) (lem-pass-CS23-vs-iI) ▸
       at 6 2 (ι ∷ CS23 ∷ []) (lem-pass-CS23-vs-iI) ▸
       at 7 2 (ι ∷ CS23 ∷ []) (lem-pass-CS23-vs-iI) ▸ done

  b1 : Chain (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ CS23 ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ CS23 ∷ [])
  b1 = at 8 2 (S0 ∷ CS23 ∷ []) (lem-pass-CS23-vs-S0) ▸
       at 9 2 (S3 ∷ CS23 ∷ []) (lem-pass-CS23-vs-S3) ▸
       at 10 2 (CS03⁻ ∷ CS23 ∷ []) (lem-pass-CS23-vs-CSd03) ▸
       at 11 2 (Toff012 ∷ CS23 ∷ []) (lem-pass-CS23-vs-TOFF012) ▸ done


-- pass [TOFF201] [iI]: 1 steps
lem-pass-TOFF201-vs-iI : ⟪ (Toff201 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-iI = run b0
  where
  b0 : Chain (Toff201 ∷ ι ∷ []) (ι ∷ Toff201 ∷ [])
  b0 = at 0 2 (ι ∷ Toff201 ∷ []) (win 3 0 complete₃ (Toffᵗ • iI) (iI • Toffᵗ) tt tt Eq.refl) ▸ done


-- pass [CSd23] [iI]: 1 steps
lem-pass-CSd23-vs-iI : ⟪ (CS23⁻ ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-CSd23-vs-iI = run b0
  where
  b0 : Chain (CS23⁻ ∷ ι ∷ []) (ι ∷ CS23⁻ ∷ [])
  b0 = at 0 2 (ι ∷ CS23⁻ ∷ []) (win 1 2 complete₃ (((CS • CS • CS) ↑) • iI) (iI • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸ done


-- pass [CS23 TOFF201 CSd23 TOFF201] [iI]: 4 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI = run b0
  where
  b0 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ ι ∷ []) (ι ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b0 = at 3 2 (ι ∷ Toff201 ∷ []) (lem-pass-TOFF201-vs-iI) ▸
       at 2 2 (ι ∷ CS23⁻ ∷ []) (lem-pass-CSd23-vs-iI) ▸
       at 1 2 (ι ∷ Toff201 ∷ []) (lem-pass-TOFF201-vs-iI) ▸
       at 0 2 (ι ∷ CS23 ∷ []) (lem-pass-CS23-vs-iI) ▸ done


-- pass [Sd0] [CSd23]: 1 steps
lem-pass-Sd0-vs-CSd23 : ⟪ (S0⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-pass-Sd0-vs-CSd23 = run b0
  where
  b0 : Chain (S0⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S0⁻ ∷ []) (win 1 2 complete₃ ((S • S • S) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (S • S • S)) tt tt Eq.refl) ▸ done

