{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD589 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D589 (W : Ws) (Sᴰ : SD589) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-X2 : St 254
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-X2 = pickᴰ 0 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd21-X2 : St 257
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd21-X2 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-X2 : St 278
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-X2 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd21-X2 : St 284
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd21-X2 = pickᴰ 3 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-X2 : St 1032
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-X2 = pickᴰ 4 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2 : St 1033
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2 = pickᴰ 5 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2 : St 1034
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2 = pickᴰ 6 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2 : St 1035
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2 = pickᴰ 7 Sᴰ
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 869
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 8 Sᴰ
  lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : St 905
  lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 9 Sᴰ
  lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 913
  lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 10 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 1043
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 11 Sᴰ
  lem-Bar⟨SSSKSS12-⟶0⟩-passes-II/IV-units-2-3 : St 1044
  lem-Bar⟨SSSKSS12-⟶0⟩-passes-II/IV-units-2-3 = pickᴰ 12 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03 : St 1045
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03 = pickᴰ 13 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : St 1046
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = pickᴰ 14 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 1047
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 15 Sᴰ
  lem-pass-X2-CK21-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 1048
  lem-pass-X2-CK21-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 16 Sᴰ
  lem-pass-X2-CKd21-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 1049
  lem-pass-X2-CKd21-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 17 Sᴰ
  lem-pass-X3-CK32-X3-vs-X0-TOFF201-CS23-TOFF201-CSd23-X0 : St 1050
  lem-pass-X3-CK32-X3-vs-X0-TOFF201-CS23-TOFF201-CSd23-X0 = pickᴰ 18 Sᴰ

private
  q1 : Eqn
  q1 = sE 254 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-X2
  q2 : Eqn
  q2 = sE 1032 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-X2
  q3 : Eqn
  q3 = sE 257 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd21-X2
  q4 : Eqn
  q4 = sE 1043 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q5 : Eqn
  q5 = sE 1033 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2

-- Bar(SSKSKK;2,1->0) passes split Gad(t=1, W=(2, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乇丘丘丶丘丘丶丘丘么丘丘丞习丽习举丘丞丘乇丘丘丷丘丘丷丘丘么丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇丘丘丶丘丘丶丘丘么丘丘丞习丽习举丘丞丘乇丘丘丷丘丘丷丘丘么丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乇丘丘丶丘丘丶丘丘么丘丘丞习丽习举丘丞丘乇丘丘丷丘丘丷丘丘么丘") (ℓ "丘乇丘丘丶丘丘丶丘丘么丘丘丞习丽习举丘丞丘乇丘丘丷丘丘丷丘丘么丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q1 ∷
   rw 3 q2 ∷
   rw 6 q2 ∷
   rw 9 q3 ∷
   rw 12 q4 ∷
   rw 20 q1 ∷
   rw 23 q5 ∷
   rw 26 q5 ∷
   rw 29 q3 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = sE 278 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-X2
  q7 : Eqn
  q7 = sE 1034 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2
  q8 : Eqn
  q8 = sE 284 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd21-X2
  q9 : Eqn
  q9 = sE 1047 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q10 : Eqn
  q10 = sE 1035 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2

-- Bar(SSSKSS;2,1->0) passes split Gad(t=1, W=(2, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乇丘丘丶丘丘丶丘丘么丘丘丞习丽习举丘丞丘乇丘丘丷丘丘丷丘丘么丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇丘丘丶丘丘丶丘丘么丘丘丞习丽习举丘丞丘乇丘丘丷丘丘丷丘丘么丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乇丘丘丶丘丘丶丘丘么丘丘丞习丽习举丘丞丘乇丘丘丷丘丘丷丘丘么丘") (ℓ "丘乇丘丘丶丘丘丶丘丘么丘丘丞习丽习举丘丞丘乇丘丘丷丘丘丷丘丘么丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q6 ∷
   rw 3 q7 ∷
   rw 6 q7 ∷
   rw 9 q8 ∷
   rw 12 q9 ∷
   rw 20 q6 ∷
   rw 23 q10 ∷
   rw 26 q10 ∷
   rw 29 q8 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = wE 1678 W
  q12 : Eqn
  q12 = wE 1671 W
  q13 : Eqn
  q13 = wE 1672 W
  q14 : Eqn
  q14 = sE 913 lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q15 : Eqn
  q15 = wE 1673 W

-- pass [X1 CSd10 X1] [X2 X3 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 X2 X3]: 7 steps
lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3 : ⟪ (ℓ "丒両丒丘丞三九中九丮丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三九中九丮丈丘丞丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3 = derive (ℓ "丒両丒丘丞三九中九丮丈丘丞") (ℓ "丘丞三九中九丮丈丘丞丒両丒")
  (rw 0 q11 ∷
   rw 1 q12 ∷
   rw 2 q13 ∷
   rw 3 q14 ∷
   rw 7 q15 ∷
   rw 8 q11 ∷
   rw 9 q12 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 1497 W
  q17 : Eqn
  q17 = wE 1683 W
  q18 : Eqn
  q18 = sE 1049 lem-pass-X2-CKd21-X2-vs-TOFF012-CS03-TOFF012-CSd03
  q19 : Eqn
  q19 = wE 1684 W

-- pass [X2 CKd21 X2] [X3 K0 S0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 Sd0 Kd0 X3]: 5 steps
lem-pass-X2-CKd21-X2-vs-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X3 : ⟪ (ℓ "丘么丘丞上丈丈下九中九丮上三三下丞") ⟫ʷ ≈ ⟪ (ℓ "丞上丈丈下九中九丮上三三下丞丘么丘") ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X3 = derive (ℓ "丘么丘丞上丈丈下九中九丮上三三下丞") (ℓ "丞上丈丈下九中九丮上三三下丞丘么丘")
  (rw 0 q16 ∷
   rw 1 q17 ∷
   rw 5 q18 ∷
   rw 9 q19 ∷
   rw 13 q16 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 1495 W
  q21 : Eqn
  q21 = wE 1685 W
  q22 : Eqn
  q22 = sE 1048 lem-pass-X2-CK21-X2-vs-TOFF012-CS03-TOFF012-CSd03
  q23 : Eqn
  q23 = wE 1686 W

-- pass [X2 CK21 X2] [X3 K0 S0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 Sd0 Kd0 X3]: 5 steps
lem-pass-X2-CK21-X2-vs-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X3 : ⟪ (ℓ "丘乇丘丞上丈丈下九中九丮上三三下丞") ⟫ʷ ≈ ⟪ (ℓ "丞上丈丈下九中九丮上三三下丞丘乇丘") ⟫ʷ
lem-pass-X2-CK21-X2-vs-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X3 = derive (ℓ "丘乇丘丞上丈丈下九中九丮上三三下丞") (ℓ "丞上丈丈下九中九丮上三三下丞丘乇丘")
  (rw 0 q20 ∷
   rw 1 q21 ∷
   rw 5 q22 ∷
   rw 9 q23 ∷
   rw 13 q20 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 1687 W
  q25 : Eqn
  q25 = wE 1688 W
  q26 : Eqn
  q26 = sE 905 lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23

-- pass [X3 CKd32 X3] [X0 TOFF201 CS23 TOFF201 CSd23 X0]: 5 steps
lem-pass-X3-CKd32-X3-vs-X0-TOFF201-CS23-TOFF201-CSd23-X0 : ⟪ (ℓ "丞乘丞丌乣义乣乊丌") ⟫ʷ ≈ ⟪ (ℓ "丌乣义乣乊丌丞乘丞") ⟫ʷ
lem-pass-X3-CKd32-X3-vs-X0-TOFF201-CS23-TOFF201-CSd23-X0 = derive (ℓ "丞乘丞丌乣义乣乊丌") (ℓ "丌乣义乣乊丌丞乘丞")
  (rw 0 q24 ∷
   rw 1 q25 ∷
   rw 1 q26 ∷
   rw 5 q25 ∷
   rw 5 q24 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q28 : Eqn
  q28 = wE 1409 W
  q29 : Eqn
  q29 = sE 1050 lem-pass-X3-CK32-X3-vs-X0-TOFF201-CS23-TOFF201-CSd23-X0
  q30 : Eqn
  q30 = wE 1410 W

-- pass [CK32] [X0 X3 TOFF201 CS23 TOFF201 CSd23 X0 X3]: 5 steps
lem-pass-CK32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : ⟪ (ℓ "乗丌丞乣义乣乊丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞乣义乣乊丌丞乗") ⟫ʷ
lem-pass-CK32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = derive (ℓ "乗丌丞乣义乣乊丌丞") (ℓ "丌丞乣义乣乊丌丞乗")
  (rw 1 q27 ∷
   rw 0 q28 ∷
   rw 1 q29 ∷
   rw 7 q30 ∷
   rw⁻ 0 q27 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 1689 W
  q32 : Eqn
  q32 = wE 1493 W
  q33 : Eqn
  q33 = wE 1494 W
  q34 : Eqn
  q34 = sE 869 lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [X2 CS21 X2] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 7 steps
lem-pass-X2-CS21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (ℓ "丘丶丘丌丞习丽习举丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞习丽习举丌丞丘丶丘") ⟫ʷ
lem-pass-X2-CS21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = derive (ℓ "丘丶丘丌丞习丽习举丌丞") (ℓ "丌丞习丽习举丌丞丘丶丘")
  (rw 0 q31 ∷
   rw 1 q32 ∷
   rw 2 q33 ∷
   rw 2 q34 ∷
   rw 6 q33 ∷
   rw 6 q31 ∷
   rw 7 q32 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = sE 1046 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3

-- Bar(SSKSKK;2,1->0) passes split Gad(t=1, W=(0, 2, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乇丘丘丶丘丘丶丘丘么丘丌丘丞习丽习举丌丘丞丘乇丘丘丷丘丘丷丘丘么丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇丘丘丶丘丘丶丘丘么丘丌丘丞习丽习举丌丘丞丘乇丘丘丷丘丘丷丘丘么丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乇丘丘丶丘丘丶丘丘么丘丌丘丞习丽习举丌丘丞丘乇丘丘丷丘丘丷丘丘么丘") (ℓ "丘乇丘丘丶丘丘丶丘丘么丘丌丘丞习丽习举丌丘丞丘乇丘丘丷丘丘丷丘丘么丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q1 ∷
   rw 3 q2 ∷
   rw 6 q2 ∷
   rw 9 q3 ∷
   rw 12 q35 ∷
   rw 22 q1 ∷
   rw 25 q5 ∷
   rw 28 q5 ∷
   rw 31 q3 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 1690 W
  q37 : Eqn
  q37 = sE 1044 lem-Bar⟨SSSKSS12-⟶0⟩-passes-II/IV-units-2-3
  q38 : Eqn
  q38 = wE 1691 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] [X1 TOFF213 X1]: 3 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-X1-TOFF213-X1 : ⟪ (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丒乥丒") ⟫ʷ ≈ ⟪ (ℓ "丒乥丒丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-X1-TOFF213-X1 = derive (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丒乥丒") (ℓ "丒乥丒丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧")
  (rw 31 q36 ∷
   rw 0 q37 ∷
   rw 0 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = wE 1 W
  q40 : Eqn
  q40 = wE 231 W
  q41 : Eqn
  q41 = wE 3 W
  q42 : Eqn
  q42 = wE 1692 W
  q43 : Eqn
  q43 = wE 115 W
  q44 : Eqn
  q44 = wE 1693 W
  q45 : Eqn
  q45 = wE 1694 W
  q46 : Eqn
  q46 = wE 1695 W
  q47 : Eqn
  q47 = sE 1045 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03
  q48 : Eqn
  q48 = wE 1342 W
  q49 : Eqn
  q49 = wE 1696 W
  q50 : Eqn
  q50 = wE 1697 W
  q51 : Eqn
  q51 = wE 154 W
  q52 : Eqn
  q52 = wE 1698 W
  q53 : Eqn
  q53 = wE 1699 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] [CS01 CS01 CK10 CS01 CX13 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03] ^inv: 211 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-ᵖinv : ⟪ (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丮乒丮丮乀丮丮丮丮丮丮丛乒丮丮丮乀両丵両両") ⟫ʷ ≈ ⟪ (ℓ "丮乒丮丮乀丮丮丮丮丮丮丛乒丮丮丮乀両丵両両丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-ᵖinv = derive (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丮乒丮丮乀丮丮丮丮丮丮丛乒丮丮丮乀両丵両両") (ℓ "丮乒丮丮乀丮丮丮丮丮丮丛乒丮丮丮乀両丵両両丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧")
  (rw 0 q39 ∷
   rw 1 q40 ∷
   rw 2 q39 ∷
   re 0 3 (ℓ "丮") ∷
   rw 3 q39 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q41 ∷
   rw 1 q39 ∷
   rw 2 q42 ∷
   rw 3 q39 ∷
   re 1 3 (ℓ "乒") ∷
   rw 4 q39 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q41 ∷
   rw 2 q39 ∷
   rw 3 q40 ∷
   rw 4 q39 ∷
   re 2 3 (ℓ "丮") ∷
   rw 5 q39 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q41 ∷
   rw 3 q39 ∷
   rw 4 q40 ∷
   rw 5 q39 ∷
   re 3 3 (ℓ "丮") ∷
   rw 6 q39 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q41 ∷
   rw 4 q43 ∷
   rw 5 q39 ∷
   rw 6 q40 ∷
   rw 7 q39 ∷
   re 5 3 (ℓ "丮") ∷
   rw 8 q39 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q41 ∷
   rw 6 q39 ∷
   rw 7 q40 ∷
   rw 8 q39 ∷
   re 6 3 (ℓ "丮") ∷
   rw 9 q39 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q41 ∷
   rw 7 q39 ∷
   rw 8 q40 ∷
   rw 9 q39 ∷
   re 7 3 (ℓ "丮") ∷
   rw 10 q39 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q41 ∷
   rw 8 q39 ∷
   rw 9 q40 ∷
   rw 10 q39 ∷
   re 8 3 (ℓ "丮") ∷
   rw 11 q39 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q41 ∷
   rw 9 q39 ∷
   rw 10 q40 ∷
   rw 11 q39 ∷
   re 9 3 (ℓ "丮") ∷
   rw 12 q39 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q41 ∷
   rw 10 q39 ∷
   rw 11 q40 ∷
   rw 12 q39 ∷
   re 10 3 (ℓ "丮") ∷
   rw 13 q39 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q41 ∷
   rw 11 q44 ∷
   rw 12 q39 ∷
   rw 13 q42 ∷
   rw 14 q39 ∷
   re 12 3 (ℓ "乒") ∷
   rw 15 q39 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q41 ∷
   rw 13 q39 ∷
   rw 14 q40 ∷
   rw 15 q39 ∷
   re 13 3 (ℓ "丮") ∷
   rw 16 q39 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q41 ∷
   rw 14 q39 ∷
   rw 15 q40 ∷
   rw 16 q39 ∷
   re 14 3 (ℓ "丮") ∷
   rw 17 q39 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q41 ∷
   rw 15 q39 ∷
   rw 16 q40 ∷
   rw 17 q39 ∷
   re 15 3 (ℓ "丮") ∷
   rw 18 q39 ∷
   re 16 3 (ℓ "中") ∷
   rw 17 q41 ∷
   rw 16 q43 ∷
   rw 17 q45 ∷
   rw 18 q46 ∷
   rw 19 q45 ∷
   rw 20 q45 ∷
   rw⁻ 21 q47 ∷
   rw 74 q39 ∷
   re 73 1 (ℓ "乏丨乏") ∷
   rw 75 q41 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q41 ∷
   rw 73 q48 ∷
   rw 72 q41 ∷
   rw 73 q39 ∷
   re 72 1 (ℓ "乏久乏") ∷
   rw 74 q41 ∷
   re 71 1 (ℓ "乏乄乏") ∷
   rw 73 q41 ∷
   rw 72 q49 ∷
   rw 71 q41 ∷
   rw 72 q39 ∷
   re 71 1 (ℓ "乏丨乏") ∷
   rw 73 q41 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q41 ∷
   rw 71 q48 ∷
   rw 70 q41 ∷
   rw 71 q39 ∷
   re 70 1 (ℓ "乏丨乏") ∷
   rw 72 q41 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q41 ∷
   rw 70 q48 ∷
   rw 69 q41 ∷
   rw 68 q50 ∷
   rw 69 q39 ∷
   re 68 1 (ℓ "乏丨乏") ∷
   rw 70 q41 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q41 ∷
   rw 68 q48 ∷
   rw 67 q41 ∷
   rw 68 q39 ∷
   re 67 1 (ℓ "乏丨乏") ∷
   rw 69 q41 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q41 ∷
   rw 67 q48 ∷
   rw 66 q41 ∷
   rw 67 q39 ∷
   re 66 1 (ℓ "乏丨乏") ∷
   rw 68 q41 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q41 ∷
   rw 66 q48 ∷
   rw 65 q41 ∷
   rw 66 q39 ∷
   re 65 1 (ℓ "乏丨乏") ∷
   rw 67 q41 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q41 ∷
   rw 65 q48 ∷
   rw 64 q41 ∷
   rw 65 q39 ∷
   re 64 1 (ℓ "乏丨乏") ∷
   rw 66 q41 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q41 ∷
   rw 64 q48 ∷
   rw 63 q41 ∷
   rw 64 q39 ∷
   re 63 1 (ℓ "乏丨乏") ∷
   rw 65 q41 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q41 ∷
   rw 63 q48 ∷
   rw 62 q41 ∷
   rw 61 q51 ∷
   rw 62 q39 ∷
   re 61 1 (ℓ "乏久乏") ∷
   rw 63 q41 ∷
   re 60 1 (ℓ "乏乄乏") ∷
   rw 62 q41 ∷
   rw 61 q49 ∷
   rw 60 q41 ∷
   rw 61 q39 ∷
   re 60 1 (ℓ "乏丨乏") ∷
   rw 62 q41 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q41 ∷
   rw 60 q48 ∷
   rw 59 q41 ∷
   rw 60 q39 ∷
   re 59 1 (ℓ "乏丨乏") ∷
   rw 61 q41 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q41 ∷
   rw 59 q48 ∷
   rw 58 q41 ∷
   rw 59 q39 ∷
   re 58 1 (ℓ "乏丨乏") ∷
   rw 60 q41 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q41 ∷
   rw 58 q48 ∷
   rw 57 q41 ∷
   rw 56 q50 ∷
   rw 55 q52 ∷
   rw 54 q53 ∷
   rw 53 q52 ∷
   rw 52 q52 ∷ []) Eq.refl
