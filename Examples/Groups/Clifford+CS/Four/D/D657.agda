{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D657 where

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
open import Examples.Groups.Clifford+CS.Four.D.D017 using (lem-S2-at1023)
open import Examples.Groups.Clifford+CS.Four.D.D072 using (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D073 using (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D088 using (lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D190 using (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12)
open import Examples.Groups.Clifford+CS.Four.D.D191 using (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12)
open import Examples.Groups.Clifford+CS.Four.D.D236 using (lem-AXIOM-LF-at0231)
open import Examples.Groups.Clifford+CS.Four.D.D266 using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-X2)
open import Examples.Groups.Clifford+CS.Four.D.D268 using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd21-X2)
open import Examples.Groups.Clifford+CS.Four.D.D281 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2)
open import Examples.Groups.Clifford+CS.Four.D.D286 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2)
open import Examples.Groups.Clifford+CS.Four.D.D348 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D350 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D507 using (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF103-X0-X3)
open import Examples.Groups.Clifford+CS.Four.D.D611 using (lem-pass-CCZ123-vs-X2-CK21-X2 ; lem-pass-CCZ123-vs-X2-CS12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D613 using (lem-pass-CCZ123-vs-X2-CKd21-X2 ; lem-pass-CCZ123-vs-X2-CSd12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D629 using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2 ; lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D630 using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-TOFF102-X2 ; lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D631 using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D646 using (lem-pass-X3-CKd32-X3-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D648 using (lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D650 using (lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D656 using (lem-b2g-0111PP1 ; lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2 ; lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3)
-- pass [X2 CKd21 X2] [X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X3]: 9 steps
lem-pass-X2-CKd21-X2-vs-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X3 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X3 ∷ []) (X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 1 7 (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑)) ((K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 17 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 14 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 11 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 8 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 5 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 9 19 (K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑)) ((K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b1 = at 13 4 (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CKd21] [X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X2 X3]: 5 steps
lem-pass-CKd21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 : ⟪ (CK21⁻ ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CK21⁻ ∷ []) ⟫ʷ
lem-pass-CKd21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 = run b0
  where
  b0 : Chain (CK21⁻ ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CK21⁻ ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 3 0 complete₃ (((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 17 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 17 (X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X3) ▸
       at 15 4 (X2 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 14 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- CCZ(2,3,1) passes split Gad(t=1, W=(2, 3), d=KSSKd, e=1): 9 steps
lem-CCZ⟨231⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨231⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (X2 ∷ CK21 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CK21-X2) ▸
       at 3 4 (X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CS12-X2) ▸
       at 6 4 (X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CS12-X2) ▸
       at 9 4 (X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CKd21-X2) ▸
       at 12 9 (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3) ▸
       at 20 4 (X2 ∷ CK21 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CK21-X2) ▸
       at 23 4 (X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CSd12-X2) ▸
       at 26 4 (X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CSd12-X2) ▸ done

  b1 : Chain (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ [])
  b1 = at 29 4 (X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CKd21-X2) ▸ done


-- pass [CCZ123] [X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X2 X3]: 3 steps
lem-pass-CCZ123-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 : ⟪ (CCZ123 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 1 16 (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2) ▸
       at 0 33 (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-CCZ⟨231⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩) ▸
       at 0 32 (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) (sym lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2) ▸ done


-- pass [X2 CK21 X2] [X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X3]: 9 steps
lem-pass-X2-CK21-X2-vs-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X3 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X3 ∷ []) (X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CK₁₀ • (X ↑)) tt tt Eq.refl) ▸
       at 1 7 (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑)) ((K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 17 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 14 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 11 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 8 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 5 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 9 19 (K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑)) ((K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ X3 ∷ []) (X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  b1 = at 13 4 (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CK₁₀ • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CK21] [X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X2 X3]: 5 steps
lem-pass-CK21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 : ⟪ (CK21 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CK21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 = run b0
  where
  b0 : Chain (CK21 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CK21 ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (win 3 0 complete₃ ((CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 17 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 17 (X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X3) ▸
       at 15 4 (X2 ∷ CK21 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 14 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [TOFF123] [X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X2 X3]: 5 steps
lem-pass-TOFF123-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 : ⟪ (Toff123 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ
lem-pass-TOFF123-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 = run b0
  where
  b0 : Chain (Toff123 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ Toff123 ∷ [])
  b0 = at 0 1 (CK21 ∷ CCZ123 ∷ CK21⁻ ∷ []) (win 0 3 complete₃ (Toff) (CK₁₀ • CCZ • (S ↑ • CK₁₀)) tt tt Eq.refl) ▸
       at 2 17 (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CK21⁻ ∷ []) (lem-pass-CKd21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3) ▸
       at 1 17 (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3) ▸
       at 0 17 (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CK21 ∷ []) (lem-pass-CK21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3) ▸
       at 16 3 (Toff123 ∷ []) (win 0 3 complete₃ (CK₁₀ • CCZ • (S ↑ • CK₁₀)) (Toff) tt tt Eq.refl) ▸ done


-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 20 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ CS13 ∷ X2 ∷ X2 ∷ X3 ∷ X2 ∷ X3 ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ [])
  b0 = at 34 0 (X2 ∷ X3 ∷ X2 ∷ X3 ∷ []) (win 0 3 complete₃ (ε) ((X ↑) • (X ↑ ↑) • (X ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 39 0 (X2 ∷ X3 ∷ X2 ∷ X3 ∷ []) (win 0 3 complete₃ (ε) ((X ↑) • (X ↑ ↑) • (X ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 44 0 (X2 ∷ X3 ∷ X2 ∷ X3 ∷ []) (win 0 3 complete₃ (ε) ((X ↑) • (X ↑ ↑) • (X ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 32 2 (Toff102 ∷ X3 ∷ []) (sym (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))) ▸
       at 33 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 34 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 34 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 35 2 (CS13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ CS13 ∷ X2 ∷ X2 ∷ X3 ∷ X2 ∷ X3 ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CS13 ∷ X3 ∷ X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  b1 = at 36 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 38 2 (Toff102 ∷ X3 ∷ []) (sym (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))) ▸
       at 39 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 40 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 40 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 41 2 (CS13⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 42 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 0 34 (X2 ∷ Toff102 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-TOFF102-X2) ▸ done

  b2 : Chain (X2 ∷ Toff102 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CS13 ∷ X3 ∷ X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b2 = at 3 34 (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS13-X3) ▸
       at 6 34 (X2 ∷ Toff102 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-TOFF102-X2) ▸
       at 9 34 (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd13-X3) ▸
       at 0 12 (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (sym lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13) ▸ done


-- Bar(SSSKSS;2,1->0) passes split Gad(t=1, W=(2, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ = trans (run b0) (run b1)
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 0 34 (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-X2) ▸
       at 3 34 (X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2) ▸
       at 6 34 (X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2) ▸
       at 9 34 (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd21-X2) ▸
       at 12 39 (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3) ▸
       at 20 34 (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-X2) ▸
       at 23 34 (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2) ▸
       at 26 34 (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2) ▸ done

  b1 : Chain (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b1 = at 29 34 (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd21-X2) ▸ done


-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X2 X3]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 = run b0
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  b0 = at 31 16 (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2) ▸
       at 0 63 (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩) ▸
       at 0 32 (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) (sym lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2) ▸ done


-- Bar(SSKSKK;2,3->0) passes split Gad(t=1, W=(2, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ = trans (run b0) (run b1)
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 0 32 (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2) ▸
       at 3 32 (X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2) ▸
       at 6 32 (X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2) ▸
       at 9 32 (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2) ▸
       at 12 37 (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3) ▸
       at 20 32 (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2) ▸
       at 23 32 (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2) ▸
       at 26 32 (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2) ▸ done

  b1 : Chain (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  b1 = at 29 32 (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2) ▸ done


-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 = run b0
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  b0 = at 29 16 (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2) ▸
       at 0 61 (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩) ▸
       at 0 32 (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) (sym lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2) ▸ done


-- far CS02 CS02 CK20 CS02 CX23 CS03 CS03 CS03 .. 0111PP1 sep 2: 9 steps
lem-far-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03-··-0111PP1-sep-2 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ X1 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ []) ⟫ʷ
lem-far-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03-··-0111PP1-sep-2 = trans (run b0) (run b1)
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ X1 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ [])
  b0 = at 80 10 (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) (lem-b2g-0111PP1) ▸
       at 0 80 (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Toff123 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ Toff123 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-AXIOM-LF-at0231) ▸
       at 62 45 (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3) ▸
       at 61 17 (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ Toff123 ∷ []) (lem-pass-TOFF123-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3) ▸
       at 30 47 (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3) ▸
       at 29 17 (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ Toff123 ∷ []) (lem-pass-TOFF123-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3) ▸
       at 0 45 (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3) ▸
       at 16 91 (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ []) (sym lem-AXIOM-LF-at0231) ▸ done

  b1 : Chain (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ [])
  b1 = at 0 16 (X1 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (sym lem-b2g-0111PP1) ▸ done


-- distribute Gad(t=1, W=(0, 3), d=1, e=1) TOFF103 CS12 TOFF103 CSd12: 14 steps
lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ X3 ∷ X3 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ [])
  b0 = at 2 4 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (lem-S2-at1023) ▸
       at 3 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑ ↑) • X • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑ ↑) • X • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 13 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑ ↑) • X • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 6 2 (CS12 ∷ X0 ∷ []) (low₁-comm (X) (CS)) ▸
       at 7 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 5 2 (CS12 ∷ X3 ∷ []) (sym (low₃-comm ((CS ↑)) (X))) ▸ done

  b1 : Chain (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ X3 ∷ X3 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ [])
  b1 = at 6 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 12 2 (CS12⁻ ∷ X0 ∷ []) (low₁-comm (X) ((CS • CS • CS))) ▸
       at 13 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 11 2 (CS12⁻ ∷ X3 ∷ []) (sym (low₃-comm (((CS • CS • CS) ↑)) (X))) ▸
       at 12 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 19 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ X3 ∷ X3 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ [])
  b0 = at 31 4 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (lem-S2-at1023) ▸
       at 32 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑ ↑) • X • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 37 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑ ↑) • X • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 42 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑ ↑) • X • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 34 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 35 2 (CS12 ∷ X0 ∷ []) (low₁-comm (X) (CS)) ▸
       at 36 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 34 2 (CS12 ∷ X3 ∷ []) (sym (low₃-comm ((CS ↑)) (X))) ▸ done

  b1 : Chain (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ X3 ∷ X3 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ [])
  b1 = at 35 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 40 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 41 2 (CS12⁻ ∷ X0 ∷ []) (low₁-comm (X) ((CS • CS • CS))) ▸
       at 42 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 40 2 (CS12⁻ ∷ X3 ∷ []) (sym (low₃-comm (((CS • CS • CS) ↑)) (X))) ▸
       at 41 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 0 34 (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF103-X0-X3) ▸
       at 5 30 (CS12 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12) ▸ done

  b2 : Chain (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  b2 = at 6 34 (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF103-X0-X3) ▸
       at 11 30 (CS12⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12) ▸
       at 0 12 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (sym lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12) ▸ done


-- pass [X3 CKd32 X3] [X0 TOFF102 CS13 TOFF102 CSd13 X0]: 5 steps
lem-pass-X3-CKd32-X3-vs-X0-TOFF102-CS13-TOFF102-CSd13-X0 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ X0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-X0-TOFF102-CS13-TOFF102-CSd13-X0 = run b0
  where
  b0 : Chain (X3 ∷ CK32⁻ ∷ X3 ∷ X0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ []) (X0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  b0 = at 0 4 (X0 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (win 1 2 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 3 (X3 ∷ CK32⁻ ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 5 3 (X3 ∷ CK32⁻ ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 4 (X0 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (win 1 2 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done

