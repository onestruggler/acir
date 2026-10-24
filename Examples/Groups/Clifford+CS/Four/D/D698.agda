{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD698 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D698 (W : Ws) (Sᴰ : SD698) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-X3 : St 1162
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-X3 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd30-X3 : St 1163
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd30-X3 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2 : St 293
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2 : St 299
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2 = pickᴰ 3 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2 : St 365
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2 = pickᴰ 4 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2 : St 367
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2 = pickᴰ 5 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-X3 : St 1871
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-X3 = pickᴰ 6 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd03-X3 : St 1872
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd03-X3 = pickᴰ 7 Sᴰ
  lem-hyb-sym-23-at0321-part1 : St 1873
  lem-hyb-sym-23-at0321-part1 = pickᴰ 8 Sᴰ
  lem-hyb-sym-23-at0321-part2 : St 1874
  lem-hyb-sym-23-at0321-part2 = pickᴰ 9 Sᴰ
  lem-hyb-sym-23-at1320-part0 : St 1875
  lem-hyb-sym-23-at1320-part0 = pickᴰ 10 Sᴰ
  lem-hyb-sym-23-at1320-part2 : St 1876
  lem-hyb-sym-23-at1320-part2 = pickᴰ 11 Sᴰ
  lem-pass-X1-CK13-X1-vs-TOFF013-CS02-TOFF013-CSd02 : St 1877
  lem-pass-X1-CK13-X1-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 12 Sᴰ
  lem-pass-X1-CKd13-X1-vs-TOFF013-CS02-TOFF013-CSd02 : St 1878
  lem-pass-X1-CKd13-X1-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 13 Sᴰ
  lem-pass-X1-CS13-X1-vs-TOFF013-CS02-TOFF013-CSd02 : St 1879
  lem-pass-X1-CS13-X1-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 14 Sᴰ
  lem-pass-X1-CSd13-X1-vs-TOFF013-CS02-TOFF013-CSd02 : St 1880
  lem-pass-X1-CSd13-X1-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 15 Sᴰ
  lem-S2 : St 1778
  lem-S2 = pickᴰ 16 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 1881
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 17 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CZ13-CCZ123 : St 1882
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CZ13-CCZ123 = pickᴰ 18 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13 : St 1883
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13 = pickᴰ 19 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Z1-CZ12-CZ13-CCZ123 : St 1884
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Z1-CZ12-CZ13-CCZ123 = pickᴰ 20 Sᴰ
  lem-pass-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3-vs-CCZ123 : St 1885
  lem-pass-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3-vs-CCZ123 = pickᴰ 21 Sᴰ
  lem-pass-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3-vs-CCZ123 : St 1886
  lem-pass-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3-vs-CCZ123 = pickᴰ 22 Sᴰ
  lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 1887
  lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 23 Sᴰ
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 1888
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 24 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1889
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 25 Sᴰ
  lem-pass-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2-vs-CCZ123 : St 1890
  lem-pass-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2-vs-CCZ123 = pickᴰ 26 Sᴰ
  lem-hyb-sym-23-at0321-part0 : St 1891
  lem-hyb-sym-23-at0321-part0 = pickᴰ 27 Sᴰ
  lem-hyb-sym-23-at1320-part1 : St 1892
  lem-hyb-sym-23-at1320-part1 = pickᴰ 28 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CZ23-CCZ123 : St 1893
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CZ23-CCZ123 = pickᴰ 29 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CCZ023 : St 1894
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CCZ023 = pickᴰ 30 Sᴰ
  lem-top-HDᵖ3 : St 1895
  lem-top-HDᵖ3 = pickᴰ 31 Sᴰ

private
  q1 : Eqn
  q1 = sE 1778 lem-S2
  q2 : Eqn
  q2 = sE 1879 lem-pass-X1-CS13-X1-vs-TOFF013-CS02-TOFF013-CSd02
  q3 : Eqn
  q3 = sE 1778 lem-S2

-- pass [X1 CS13 X1] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X1-CS13-X1-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丒丽丒九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丒丽丒") ⟫ʷ
lem-pass-X1-CS13-X1-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丒丽丒九中九丮") (ℓ "九中九丮丒丽丒")
  (rw 3 q1 ∷
   rw 0 q2 ∷
   rw⁻ 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = sE 1877 lem-pass-X1-CK13-X1-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [X1 CK13 X1] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X1-CK13-X1-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丒乁丒九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丒乁丒") ⟫ʷ
lem-pass-X1-CK13-X1-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丒乁丒九中九丮") (ℓ "九中九丮丒乁丒")
  (rw 3 q1 ∷
   rw 0 q4 ∷
   rw⁻ 0 q3 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = sE 1880 lem-pass-X1-CSd13-X1-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [X1 CSd13 X1] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X1-CSd13-X1-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丒举丒九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丒举丒") ⟫ʷ
lem-pass-X1-CSd13-X1-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丒举丒九中九丮") (ℓ "九中九丮丒举丒")
  (rw 3 q1 ∷
   rw 0 q5 ∷
   rw⁻ 0 q3 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = sE 1886 lem-pass-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3-vs-CCZ123

-- pass [CCZ123] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 1 steps
lem-pass-CCZ123-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (ℓ "乜丒丘丞九中九丮丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞九中九丮丒丘丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = derive (ℓ "乜丒丘丞九中九丮丒丘丞") (ℓ "丒丘丞九中九丮丒丘丞乜")
  (rw⁻ 0 q6 ∷ []) Eq.refl

private
  q7 : Eqn
  q7 = sE 1878 lem-pass-X1-CKd13-X1-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [X1 CKd13 X1] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X1-CKd13-X1-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丒乂丒九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丒乂丒") ⟫ʷ
lem-pass-X1-CKd13-X1-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丒乂丒九中九丮") (ℓ "九中九丮丒乂丒")
  (rw 3 q1 ∷
   rw 0 q7 ∷
   rw⁻ 0 q3 ∷ []) Eq.refl

private
  q8 : Eqn
  q8 = sE 293 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2
  q9 : Eqn
  q9 = sE 365 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2
  q10 : Eqn
  q10 = sE 299 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2
  q11 : Eqn
  q11 = sE 1881 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q12 : Eqn
  q12 = sE 367 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2

-- Bar(SSKSKK;2,3->0) passes split Gad(t=1, W=(2, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乇丘丘丶丘丘丶丘丘么丘丘丞习丽习举丘丞丘乇丘丘丷丘丘丷丘丘么丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇丘丘丶丘丘丶丘丘么丘丘丞习丽习举丘丞丘乇丘丘丷丘丘丷丘丘么丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乇丘丘丶丘丘丶丘丘么丘丘丞习丽习举丘丞丘乇丘丘丷丘丘丷丘丘么丘") (ℓ "丘乇丘丘丶丘丘丶丘丘么丘丘丞习丽习举丘丞丘乇丘丘丷丘丘丷丘丘么丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 0 q8 ∷
   rw 3 q9 ∷
   rw 6 q9 ∷
   rw 9 q10 ∷
   rw 12 q11 ∷
   rw 20 q8 ∷
   rw 23 q12 ∷
   rw 26 q12 ∷
   rw 29 q10 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 1985 W
  q14 : Eqn
  q14 = wE 1986 W
  q15 : Eqn
  q15 = wE 1987 W
  q16 : Eqn
  q16 = sE 1884 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Z1-CZ12-CZ13-CCZ123
  q17 : Eqn
  q17 = eqn (ℓ "专丞") (ℓ "丞专") (low-comm ((Z ↑)) ((X ↑)))
  q18 : Eqn
  q18 = eqn (ℓ "丸丞") (ℓ "丞丸") (low₃-comm ((CZ ↑)) (X))
  q19 : Eqn
  q19 = wE 1988 W
  q20 : Eqn
  q20 = eqn (ℓ "专丘") (ℓ "丘专") (low-comm ((Z ↑)) (X))
  q21 : Eqn
  q21 = wE 1989 W
  q22 : Eqn
  q22 = wE 1990 W

-- pass [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3] [CCZ123]: 15 steps
lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CCZ123 : ⟪ (ℓ "丘丞九中九丮丘丞乜") ⟫ʷ ≈ ⟪ (ℓ "乜丘丞九中九丮丘丞") ⟫ʷ
lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CCZ123 = derive (ℓ "丘丞九中九丮丘丞乜") (ℓ "乜丘丞九中九丮丘丞")
  (rw 7 q13 ∷
   rw 6 q14 ∷
   rw 8 q15 ∷
   rw 2 q16 ∷
   rw⁻ 1 q17 ∷
   rw⁻ 2 q18 ∷
   rw 3 q19 ∷
   rw 5 q13 ∷
   rw⁻ 0 q20 ∷
   rw 1 q14 ∷
   rw⁻ 3 q20 ∷
   rw 4 q21 ∷
   rw 5 q14 ∷
   rw 7 q15 ∷
   rw 0 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = sE 1885 lem-pass-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3-vs-CCZ123

-- pass [CCZ123] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 1 steps
lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (ℓ "乜丌丘丞习丽习举丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞习丽习举丌丘丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = derive (ℓ "乜丌丘丞习丽习举丌丘丞") (ℓ "丌丘丞习丽习举丌丘丞乜")
  (rw⁻ 0 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 1958 W
  q25 : Eqn
  q25 = sE 1883 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13
  q26 : Eqn
  q26 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q27 : Eqn
  q27 = wE 1959 W
  q28 : Eqn
  q28 = wE 1960 W

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [CS13]: 5 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS13 : ⟪ (ℓ "丞中九丮九丞丽") ⟫ʷ ≈ ⟪ (ℓ "丽丞中九丮九丞") ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS13 = derive (ℓ "丞中九丮九丞丽") (ℓ "丽丞中九丮九丞")
  (rw 5 q24 ∷
   rw 1 q25 ∷
   rw⁻ 0 q26 ∷
   rw 1 q27 ∷
   rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = sE 1887 lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [CS13 TOFF102 CSd13 TOFF102] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (ℓ "丽习举习丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘丽习举习") ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (ℓ "丽习举习丘中九丮九丘") (ℓ "丘中九丮九丘丽习举习")
  (rw⁻ 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = sE 1888 lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [CS13 TOFF102 CSd13 TOFF102] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "丽习举习丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞丽习举习") ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "丽习举习丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞丽习举习")
  (rw⁻ 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = sE 1882 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CZ13-CCZ123
  q32 : Eqn
  q32 = wE 2006 W

-- pass [X2 CS03 TOFF012 CSd03 TOFF012 X2] [CCZ123]: 5 steps
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CCZ123 : ⟪ (ℓ "丘中九丮九丘乜") ⟫ʷ ≈ ⟪ (ℓ "乜丘中九丮九丘") ⟫ʷ
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CCZ123 = derive (ℓ "丘中九丮九丘乜") (ℓ "乜丘中九丮九丘")
  (rw 5 q15 ∷
   rw 1 q31 ∷
   rw 0 q21 ∷
   rw 1 q15 ∷
   rw 0 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = sE 1872 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd03-X3
  q34 : Eqn
  q34 = sE 1163 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd30-X3
  q35 : Eqn
  q35 = sE 1871 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-X3
  q36 : Eqn
  q36 = sE 1889 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q37 : Eqn
  q37 = sE 1162 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-X3

-- Bar(SSKSKK;3,2->0) passes split Gad(t=0, W=(2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丮丞丞乒丞丞中丞丞中丞丘丞中九丮九丘丞丞丮丞丞丮丞丞乑丞丞中丞") ⟫ʷ ≈ ⟪ (ℓ "丞丮丞丞乒丞丞中丞丞中丞丘丞中九丮九丘丞丞丮丞丞丮丞丞乑丞丞中丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丮丞丞乒丞丞中丞丞中丞丘丞中九丮九丘丞丞丮丞丞丮丞丞乑丞丞中丞") (ℓ "丞丮丞丞乒丞丞中丞丞中丞丘丞中九丮九丘丞丞丮丞丞丮丞丞乑丞丞中丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q33 ∷
   rw 3 q34 ∷
   rw 6 q35 ∷
   rw 9 q35 ∷
   rw 12 q36 ∷
   rw 20 q33 ∷
   rw 23 q33 ∷
   rw 26 q37 ∷
   rw 29 q35 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = sE 1890 lem-pass-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2-vs-CCZ123

-- pass [CCZ123] [X0 X2 CS13 TOFF102 CSd13 TOFF102 X0 X2]: 1 steps
lem-pass-CCZ123-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : ⟪ (ℓ "乜丌丘丽习举习丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丽习举习丌丘乜") ⟫ʷ
lem-pass-CCZ123-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = derive (ℓ "乜丌丘丽习举习丌丘") (ℓ "丌丘丽习举习丌丘乜")
  (rw⁻ 0 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = sE 1891 lem-hyb-sym-23-at0321-part0
  q40 : Eqn
  q40 = sE 1873 lem-hyb-sym-23-at0321-part1
  q41 : Eqn
  q41 = sE 1874 lem-hyb-sym-23-at0321-part2

-- hyb sym 23 @0321: 3 steps
lem-hyb-sym-23-at0321 : ⟪ (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临") ⟫ʷ ≈ ⟪ (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄") ⟫ʷ
lem-hyb-sym-23-at0321 = derive (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临") (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄")
  (rw 0 q39 ∷
   rw 0 q40 ∷
   rw 0 q41 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = sE 1875 lem-hyb-sym-23-at1320-part0
  q43 : Eqn
  q43 = sE 1892 lem-hyb-sym-23-at1320-part1
  q44 : Eqn
  q44 = sE 1876 lem-hyb-sym-23-at1320-part2

-- hyb sym 23 @1320: 3 steps
lem-hyb-sym-23-at1320 : ⟪ (ℓ "丽丽乔丽乖丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶两丶丶丶且乇丶丶丶丶丶丶乖丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶且且且且乇丶丶丶丶丶丶丶丶丶乖丽丽丽业乔丽丽丽丽丽丽丈两") ⟫ʷ ≈ ⟪ (ℓ "丽丽乔丽乐丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠乇丠丠丠丈两丠丠丠丠丠丠乐丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈丈两丠丠丠丠丠丠丠丠丠乐丽丽丽业乔丽丽丽丽丽丽且乇") ⟫ʷ
lem-hyb-sym-23-at1320 = derive (ℓ "丽丽乔丽乖丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶两丶丶丶且乇丶丶丶丶丶丶乖丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶且且且且乇丶丶丶丶丶丶丶丶丶乖丽丽丽业乔丽丽丽丽丽丽丈两") (ℓ "丽丽乔丽乐丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠乇丠丠丠丈两丠丠丠丠丠丠乐丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈丈两丠丠丠丠丠丠丠丠丠乐丽丽丽业乔丽丽丽丽丽丽且乇")
  (rw 0 q42 ∷
   rw 0 q43 ∷
   rw 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 387 W
  q46 : Eqn
  q46 = sE 1895 lem-top-HDᵖ3

-- top k^3: 4 steps
lem-top-kᵖ3 : ⟪ (ℓ "丌丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丌丌丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丌丌丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丌") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-top-kᵖ3 = derive (ℓ "丌丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丌丌丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丌丌丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丌") []
  (rw 81 q45 ∷
   rw 161 q45 ∷
   rw 1 q46 ∷
   rw 0 q45 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = sE 1894 lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CCZ023

-- pass [TOFF012 CS03 TOFF012 CSd03] [CCZ023]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CCZ023 : ⟪ (ℓ "九中九丮乛") ⟫ʷ ≈ ⟪ (ℓ "乛九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CCZ023 = derive (ℓ "九中九丮乛") (ℓ "乛九中九丮")
  (rw 0 q1 ∷
   rw 0 q47 ∷
   rw⁻ 1 q3 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 1996 W
  q49 : Eqn
  q49 = sE 1893 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CZ23-CCZ123
  q50 : Eqn
  q50 = eqn (ℓ "丒之") (ℓ "之丒") (low-comm ((X ↑)) (CZ))
  q51 : Eqn
  q51 = wE 2039 W

-- pass [X1 TOFF012 CS03 TOFF012 CSd03 X1] [CCZ123]: 5 steps
lem-pass-X1-TOFF012-CS03-TOFF012-CSd03-X1-vs-CCZ123 : ⟪ (ℓ "丒九中九丮丒乜") ⟫ʷ ≈ ⟪ (ℓ "乜丒九中九丮丒") ⟫ʷ
lem-pass-X1-TOFF012-CS03-TOFF012-CSd03-X1-vs-CCZ123 = derive (ℓ "丒九中九丮丒乜") (ℓ "乜丒九中九丮丒")
  (rw 5 q48 ∷
   rw 1 q49 ∷
   rw 0 q50 ∷
   rw 1 q48 ∷
   rw 0 q51 ∷ []) Eq.refl
