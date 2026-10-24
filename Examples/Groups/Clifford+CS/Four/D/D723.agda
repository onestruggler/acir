{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD723 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D723 (W : Ws) (Sᴰ : SD723) where

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
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12 : St 200
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12 : St 201
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2 : St 293
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2 : St 299
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2 = pickᴰ 3 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2 : St 365
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2 = pickᴰ 4 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2 : St 367
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2 = pickᴰ 5 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CS12 : St 397
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CS12 = pickᴰ 6 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CSd12 : St 399
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CSd12 = pickᴰ 7 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-X2 : St 430
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-X2 = pickᴰ 8 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd21-X2 : St 431
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd21-X2 = pickᴰ 9 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-X2 : St 446
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-X2 = pickᴰ 10 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-X2 : St 448
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-X2 = pickᴰ 11 Sᴰ
  lem-pass-CCZ123-vs-X3-CK30-X3 : St 2109
  lem-pass-CCZ123-vs-X3-CK30-X3 = pickᴰ 12 Sᴰ
  lem-pass-CCZ123-vs-X3-CKd30-X3 : St 2110
  lem-pass-CCZ123-vs-X3-CKd30-X3 = pickᴰ 13 Sᴰ
  lem-pass-CCZ123-vs-X3-CS03-X3 : St 2111
  lem-pass-CCZ123-vs-X3-CS03-X3 = pickᴰ 14 Sᴰ
  lem-pass-CCZ123-vs-X3-CSd03-X3 : St 2112
  lem-pass-CCZ123-vs-X3-CSd03-X3 = pickᴰ 15 Sᴰ
  lem-pass-CCZ123-vs-X2-CKd20-X2 : St 2131
  lem-pass-CCZ123-vs-X2-CKd20-X2 = pickᴰ 16 Sᴰ
  lem-pass-CCZ123-vs-X2-CS02-X2 : St 2132
  lem-pass-CCZ123-vs-X2-CS02-X2 = pickᴰ 17 Sᴰ
  lem-pass-CCZ123-vs-X2-CSd02-X2 : St 2133
  lem-pass-CCZ123-vs-X2-CSd02-X2 = pickᴰ 18 Sᴰ
  lem-pass-CCZ123-vs-X2-CK20-X2 : St 2134
  lem-pass-CCZ123-vs-X2-CK20-X2 = pickᴰ 19 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF203-X0-X3 : St 2173
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF203-X0-X3 = pickᴰ 20 Sᴰ
  lem-pass-X2-CK23-X2-vs-CS01-TOFF023-CSd01-TOFF023 : St 2174
  lem-pass-X2-CK23-X2-vs-CS01-TOFF023-CSd01-TOFF023 = pickᴰ 21 Sᴰ
  lem-pass-X2-CKd23-X2-vs-CS01-TOFF023-CSd01-TOFF023 : St 2175
  lem-pass-X2-CKd23-X2-vs-CS01-TOFF023-CSd01-TOFF023 = pickᴰ 22 Sᴰ
  lem-pass-X3-CS32-X3-vs-CS01-TOFF123-CSd01-TOFF123 : St 2176
  lem-pass-X3-CS32-X3-vs-CS01-TOFF123-CSd01-TOFF123 = pickᴰ 23 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CS01-TOFF123-CSd01-TOFF123 : St 2177
  lem-pass-X3-CSd32-X3-vs-CS01-TOFF123-CSd01-TOFF123 = pickᴰ 24 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 25 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 1146
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 26 Sᴰ
  lem-S2-at2013 : St 1942
  lem-S2-at2013 = pickᴰ 27 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF203-X0-X3 : St 2178
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF203-X0-X3 = pickᴰ 28 Sᴰ
  lem-S2-at0213-ᵖ-1 : St 2024
  lem-S2-at0213-ᵖ-1 = pickᴰ 29 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2034
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 30 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2046
  lem-pass-X3-CKd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 31 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2038
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 32 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2049
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 33 Sᴰ
  lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2059
  lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 34 Sᴰ
  lem-pass-X3-CSd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2060
  lem-pass-X3-CSd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 35 Sᴰ
  lem-S2-at1023-ᵖ-1 : St 2083
  lem-S2-at1023-ᵖ-1 = pickᴰ 36 Sᴰ
  lem-S2-at1203-ᵖ-1 : St 2084
  lem-S2-at1203-ᵖ-1 = pickᴰ 37 Sᴰ
  lem-pass-CCZ123-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2123
  lem-pass-CCZ123-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 38 Sᴰ
  lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2145
  lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 39 Sᴰ
  lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2146
  lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 40 Sᴰ
  lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2147
  lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 41 Sᴰ
  lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2148
  lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 42 Sᴰ
  lem-distribute-Gad⟨t≡2-W≡⟨0-3⟩-d≡1-e≡1⟩-TOFF203-CS12-TOFF203-CSd12 : St 2164
  lem-distribute-Gad⟨t≡2-W≡⟨0-3⟩-d≡1-e≡1⟩-TOFF203-CS12-TOFF203-CSd12 = pickᴰ 43 Sᴰ
  lem-pass-CCZ123-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2179
  lem-pass-CCZ123-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 44 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : St 2180
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = pickᴰ 45 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : St 2181
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = pickᴰ 46 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : St 2182
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = pickᴰ 47 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : St 2183
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = pickᴰ 48 Sᴰ

private
  q1 : Eqn
  q1 = sE 1942 lem-S2-at2013
  q2 : Eqn
  q2 = wE 2071 W
  q3 : Eqn
  q3 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "丌丶") (ℓ "丶丌") (low₁-comm (X) (CS))
  q5 : Eqn
  q5 = wE 387 W
  q6 : Eqn
  q6 = eqn (ℓ "丶丞") (ℓ "丞丶") (low₃-comm ((CS ↑)) (X))
  q7 : Eqn
  q7 = wE 390 W
  q8 : Eqn
  q8 = eqn (ℓ "丌丷") (ℓ "丷丌") (low₁-comm (X) ((CS • CS • CS)))
  q9 : Eqn
  q9 = eqn (ℓ "丷丞") (ℓ "丞丷") (low₃-comm (((CS • CS • CS) ↑)) (X))
  q10 : Eqn
  q10 = sE 2178 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF203-X0-X3
  q11 : Eqn
  q11 = sE 397 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CS12
  q12 : Eqn
  q12 = sE 399 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CSd12
  q13 : Eqn
  q13 = sE 2164 lem-distribute-Gad⟨t≡2-W≡⟨0-3⟩-d≡1-e≡1⟩-TOFF203-CS12-TOFF203-CSd12

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X0 X3 TOFF201 CS23 TOFF201 CSd23 X0 X3]: 19 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丌丞乣义乣乊丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞乣义乣乊丌丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丌丞乣义乣乊丌丞") (ℓ "丌丞乣义乣乊丌丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 33 q1 ∷
   rw 34 q2 ∷
   rw 39 q2 ∷
   rw 44 q2 ∷
   rw 36 q3 ∷
   rw 37 q4 ∷
   rw 38 q5 ∷
   rw⁻ 36 q6 ∷
   rw 37 q7 ∷
   rw 42 q3 ∷
   rw 43 q8 ∷
   rw 44 q5 ∷
   rw⁻ 42 q9 ∷
   rw 43 q7 ∷
   rw 0 q10 ∷
   rw 5 q11 ∷
   rw 6 q10 ∷
   rw 11 q12 ∷
   rw⁻ 0 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = sE 2173 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF203-X0-X3
  q15 : Eqn
  q15 = sE 200 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12
  q16 : Eqn
  q16 = sE 201 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X0 X3 TOFF201 CS23 TOFF201 CSd23 X0 X3]: 19 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞乣义乣乊丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞乣义乣乊丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞乣义乣乊丌丞") (ℓ "丌丞乣义乣乊丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 31 q1 ∷
   rw 32 q2 ∷
   rw 37 q2 ∷
   rw 42 q2 ∷
   rw 34 q3 ∷
   rw 35 q4 ∷
   rw 36 q5 ∷
   rw⁻ 34 q6 ∷
   rw 35 q7 ∷
   rw 40 q3 ∷
   rw 41 q8 ∷
   rw 42 q5 ∷
   rw⁻ 40 q9 ∷
   rw 41 q7 ∷
   rw 0 q14 ∷
   rw 5 q15 ∷
   rw 6 q14 ∷
   rw 11 q16 ∷
   rw⁻ 0 q13 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = wE 1533 W
  q18 : Eqn
  q18 = wE 1495 W
  q19 : Eqn
  q19 = wE 1496 W
  q20 : Eqn
  q20 = sE 2059 lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [X2 CK21 X2] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 7 steps
lem-pass-X2-CK21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (ℓ "丘乇丘丌丞习丽习举丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞习丽习举丌丞丘乇丘") ⟫ʷ
lem-pass-X2-CK21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = derive (ℓ "丘乇丘丌丞习丽习举丌丞") (ℓ "丌丞习丽习举丌丞丘乇丘")
  (rw 0 q17 ∷
   rw 1 q18 ∷
   rw 2 q19 ∷
   rw 2 q20 ∷
   rw 6 q19 ∷
   rw 6 q17 ∷
   rw 7 q18 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = sE 293 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2
  q22 : Eqn
  q22 = sE 365 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2
  q23 : Eqn
  q23 = sE 299 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2
  q24 : Eqn
  q24 = sE 2181 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3
  q25 : Eqn
  q25 = sE 367 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2

-- Bar(SSKSKK;2,3->0) passes split Gad(t=1, W=(0, 2, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乇丘丘丶丘丘丶丘丘么丘丌丘丞习丽习举丌丘丞丘乇丘丘丷丘丘丷丘丘么丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇丘丘丶丘丘丶丘丘么丘丌丘丞习丽习举丌丘丞丘乇丘丘丷丘丘丷丘丘么丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乇丘丘丶丘丘丶丘丘么丘丌丘丞习丽习举丌丘丞丘乇丘丘丷丘丘丷丘丘么丘") (ℓ "丘乇丘丘丶丘丘丶丘丘么丘丌丘丞习丽习举丌丘丞丘乇丘丘丷丘丘丷丘丘么丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 0 q21 ∷
   rw 3 q22 ∷
   rw 6 q22 ∷
   rw 9 q23 ∷
   rw 12 q24 ∷
   rw 22 q21 ∷
   rw 25 q25 ∷
   rw 28 q25 ∷
   rw 31 q23 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 2165 W
  q27 : Eqn
  q27 = wE 2171 W
  q28 : Eqn
  q28 = sE 2147 lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q29 : Eqn
  q29 = sE 2145 lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q30 : Eqn
  q30 = sE 2148 lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q31 : Eqn
  q31 = wE 2172 W
  q32 : Eqn
  q32 = wE 2166 W

-- pass [X2 CKd23 X2] [X0 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X0 X3]: 9 steps
lem-pass-X2-CKd23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3 : ⟪ (ℓ "丘乎丘丌丞丐与与丑习丽习举丐丏丏丑丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丐与与丑习丽习举丐丏丏丑丌丞丘乎丘") ⟫ʷ
lem-pass-X2-CKd23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3 = derive (ℓ "丘乎丘丌丞丐与与丑习丽习举丐丏丏丑丌丞") (ℓ "丌丞丐与与丑习丽习举丐丏丏丑丌丞丘乎丘")
  (rw 0 q26 ∷
   rw 2 q27 ∷
   rw 18 q28 ∷
   rw 15 q29 ∷
   rw 12 q30 ∷
   rw 9 q29 ∷
   rw 6 q28 ∷
   rw 10 q31 ∷
   rw 14 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 2167 W
  q34 : Eqn
  q34 = wE 2173 W
  q35 : Eqn
  q35 = sE 2146 lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q36 : Eqn
  q36 = wE 2174 W
  q37 : Eqn
  q37 = wE 2168 W

-- pass [X2 CK23 X2] [X0 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X0 X3]: 9 steps
lem-pass-X2-CK23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3 : ⟪ (ℓ "丘乍丘丌丞丐与与丑习丽习举丐丏丏丑丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丐与与丑习丽习举丐丏丏丑丌丞丘乍丘") ⟫ʷ
lem-pass-X2-CK23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3 = derive (ℓ "丘乍丘丌丞丐与与丑习丽习举丐丏丏丑丌丞") (ℓ "丌丞丐与与丑习丽习举丐丏丏丑丌丞丘乍丘")
  (rw 0 q33 ∷
   rw 2 q34 ∷
   rw 18 q30 ∷
   rw 15 q35 ∷
   rw 12 q28 ∷
   rw 9 q35 ∷
   rw 6 q30 ∷
   rw 10 q36 ∷
   rw 14 q37 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = sE 430 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-X2
  q39 : Eqn
  q39 = sE 446 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-X2
  q40 : Eqn
  q40 = sE 431 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd21-X2
  q41 : Eqn
  q41 = sE 2183 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3
  q42 : Eqn
  q42 = sE 448 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-X2

-- Bar(SSSKSS;2,3->0) passes split Gad(t=1, W=(0, 2, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乇丘丘丶丘丘丶丘丘么丘丌丘丞习丽习举丌丘丞丘乇丘丘丷丘丘丷丘丘么丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇丘丘丶丘丘丶丘丘么丘丌丘丞习丽习举丌丘丞丘乇丘丘丷丘丘丷丘丘么丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乇丘丘丶丘丘丶丘丘么丘丌丘丞习丽习举丌丘丞丘乇丘丘丷丘丘丷丘丘么丘") (ℓ "丘乇丘丘丶丘丘丶丘丘么丘丌丘丞习丽习举丌丘丞丘乇丘丘丷丘丘丷丘丘么丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 0 q38 ∷
   rw 3 q39 ∷
   rw 6 q39 ∷
   rw 9 q40 ∷
   rw 12 q41 ∷
   rw 22 q38 ∷
   rw 25 q42 ∷
   rw 28 q42 ∷
   rw 31 q40 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 1376 W
  q44 : Eqn
  q44 = wE 1377 W
  q45 : Eqn
  q45 = wE 1378 W
  q46 : Eqn
  q46 = sE 2060 lem-pass-X3-CSd31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q47 : Eqn
  q47 = wE 1379 W
  q48 : Eqn
  q48 = wE 1380 W
  q49 : Eqn
  q49 = wE 1381 W

-- pass [X3 CSd31 X3] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X3-CSd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丞举丞丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丞举丞") ⟫ʷ
lem-pass-X3-CSd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丞举丞丽习举习") (ℓ "丽习举习丞举丞")
  (rw 0 q43 ∷
   rw 1 q44 ∷
   rw 2 q45 ∷
   rw 3 q44 ∷
   rw⁻ 4 q46 ∷
   rw 10 q47 ∷
   rw 9 q48 ∷
   rw 8 q49 ∷
   rw 7 q48 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = sE 2112 lem-pass-CCZ123-vs-X3-CSd03-X3
  q51 : Eqn
  q51 = sE 2110 lem-pass-CCZ123-vs-X3-CKd30-X3
  q52 : Eqn
  q52 = sE 2111 lem-pass-CCZ123-vs-X3-CS03-X3
  q53 : Eqn
  q53 = sE 2123 lem-pass-CCZ123-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q54 : Eqn
  q54 = sE 2109 lem-pass-CCZ123-vs-X3-CK30-X3

-- CCZ(3,1,2) passes split Gad(t=0, W=(3,), d=SdKdSS, e=-1): 9 steps
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "乜丞丮丞丞乒丞丞中丞丞中丞丞中九丮九丞丞丮丞丞丮丞丞乑丞丞中丞") ⟫ʷ ≈ ⟪ (ℓ "丞丮丞丞乒丞丞中丞丞中丞丞中九丮九丞丞丮丞丞丮丞丞乑丞丞中丞乜") ⟫ʷ
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "乜丞丮丞丞乒丞丞中丞丞中丞丞中九丮九丞丞丮丞丞丮丞丞乑丞丞中丞") (ℓ "丞丮丞丞乒丞丞中丞丞中丞丞中九丮九丞丞丮丞丞丮丞丞乑丞丞中丞乜")
  (rw 0 q50 ∷
   rw 3 q51 ∷
   rw 6 q52 ∷
   rw 9 q52 ∷
   rw 12 q53 ∷
   rw 18 q50 ∷
   rw 21 q50 ∷
   rw 24 q54 ∷
   rw 27 q52 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = wE 5 W
  q56 : Eqn
  q56 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q57 : Eqn
  q57 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q58 : Eqn
  q58 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q59 : Eqn
  q59 = wE 76 W
  q60 : Eqn
  q60 = wE 2063 W
  q61 : Eqn
  q61 = wE 29 W
  q62 : Eqn
  q62 = wE 31 W
  q63 : Eqn
  q63 = wE 1 W
  q64 : Eqn
  q64 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q65 : Eqn
  q65 = wE 173 W
  q66 : Eqn
  q66 = wE 3 W
  q67 : Eqn
  q67 = wE 1667 W
  q68 : Eqn
  q68 = wE 175 W
  q69 : Eqn
  q69 = sE 2049 lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q70 : Eqn
  q70 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q71 : Eqn
  q71 = wE 1668 W

-- pass [X3 CSd30 X3] [X2 Sd0 CS03 TOFF012 CSd03 TOFF012 S0 X2]: 65 steps
lem-pass-X3-CSd30-X3-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 : ⟪ (ℓ "丞丮丞丘三中九丮九丈丘") ⟫ʷ ≈ ⟪ (ℓ "丘三中九丮九丈丘丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 = derive (ℓ "丞丮丞丘三中九丮九丈丘") (ℓ "丘三中九丮九丈丘丞丮丞")
  (rw 4 q55 ∷
   rw⁻ 3 q56 ∷
   rw⁻ 2 q57 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw⁻ 3 q58 ∷
   rw 2 q59 ∷
   rw⁻ 1 q58 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 0 q57 ∷
   rw 1 q60 ∷
   rw 0 q56 ∷
   rw 1 q57 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q58 ∷
   rw 3 q61 ∷
   rw 4 q58 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q57 ∷
   rw 4 q62 ∷
   rw 5 q63 ∷
   rw 4 q64 ∷
   rw 3 q65 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q66 ∷
   rw 1 q65 ∷
   rw 2 q67 ∷
   rw⁻ 1 q64 ∷
   rw 2 q68 ∷
   rw 5 q63 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q68 ∷
   rw 5 q66 ∷
   rw 2 q69 ∷
   rw 10 q63 ∷
   rw 9 q70 ∷
   rw 8 q65 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 9 q66 ∷
   rw 6 q65 ∷
   rw 7 q71 ∷
   rw⁻ 6 q70 ∷
   rw 7 q68 ∷
   rw 10 q63 ∷
   re 8 3 (ℓ "丮") ∷
   rw 9 q68 ∷
   rw 10 q66 ∷
   rw 11 q55 ∷
   rw⁻ 10 q56 ∷
   rw⁻ 9 q57 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw⁻ 10 q58 ∷
   rw 9 q59 ∷
   rw⁻ 8 q58 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 7 q57 ∷
   rw 8 q60 ∷
   rw 7 q56 ∷
   rw 8 q57 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q58 ∷
   rw 10 q61 ∷
   rw 11 q58 ∷
   re 9 3 (ℓ "丮") ∷
   rw 10 q57 ∷
   rw 11 q62 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = sE 2024 lem-S2-at0213-ᵖ-1
  q73 : Eqn
  q73 = sE 2175 lem-pass-X2-CKd23-X2-vs-CS01-TOFF023-CSd01-TOFF023
  q74 : Eqn
  q74 = sE 2024 lem-S2-at0213-ᵖ-1

-- pass [X2 CKd23 X2] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X2-CKd23-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丘乎丘中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丘乎丘") ⟫ʷ
lem-pass-X2-CKd23-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丘乎丘中九丮九") (ℓ "中九丮九丘乎丘")
  (rw 3 q72 ∷
   rw 0 q73 ∷
   rw⁻ 0 q74 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = sE 2133 lem-pass-CCZ123-vs-X2-CSd02-X2
  q76 : Eqn
  q76 = sE 2131 lem-pass-CCZ123-vs-X2-CKd20-X2
  q77 : Eqn
  q77 = sE 2132 lem-pass-CCZ123-vs-X2-CS02-X2
  q78 : Eqn
  q78 = sE 2179 lem-pass-CCZ123-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q79 : Eqn
  q79 = sE 2134 lem-pass-CCZ123-vs-X2-CK20-X2

-- CCZ(2,1,3) passes split Gad(t=0, W=(2,), d=SdKdSS, e=-1): 9 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "乜丘丨丘丘久丘丘丧丘丘丧丘丘中九丮九丘丘丨丘丘丨丘丘乄丘丘丧丘") ⟫ʷ ≈ ⟪ (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘中九丮九丘丘丨丘丘丨丘丘乄丘丘丧丘乜") ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "乜丘丨丘丘久丘丘丧丘丘丧丘丘中九丮九丘丘丨丘丘丨丘丘乄丘丘丧丘") (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘中九丮九丘丘丨丘丘丨丘丘乄丘丘丧丘乜")
  (rw 0 q75 ∷
   rw 3 q76 ∷
   rw 6 q77 ∷
   rw 9 q77 ∷
   rw 12 q78 ∷
   rw 18 q75 ∷
   rw 21 q75 ∷
   rw 24 q79 ∷
   rw 27 q77 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = sE 2174 lem-pass-X2-CK23-X2-vs-CS01-TOFF023-CSd01-TOFF023

-- pass [X2 CK23 X2] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X2-CK23-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丘乍丘中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丘乍丘") ⟫ʷ
lem-pass-X2-CK23-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丘乍丘中九丮九") (ℓ "中九丮九丘乍丘")
  (rw 3 q72 ∷
   rw 0 q80 ∷
   rw⁻ 0 q74 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = wE 2061 W
  q82 : Eqn
  q82 = sE 1131 lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q83 : Eqn
  q83 = sE 2034 lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q84 : Eqn
  q84 = wE 2062 W

-- pass [X2 CSd20 X2] [Kd0 CS03 TOFF012 CSd03 TOFF012 K0]: 5 steps
lem-pass-X2-CSd20-X2-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 : ⟪ (ℓ "丘丨丘下中九丮九上") ⟫ʷ ≈ ⟪ (ℓ "下中九丮九上丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 = derive (ℓ "丘丨丘下中九丮九上") (ℓ "下中九丮九上丘丨丘")
  (rw 0 q81 ∷
   rw 7 q82 ∷
   rw 4 q83 ∷
   rw 1 q82 ∷
   rw 5 q84 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 137 W
  q86 : Eqn
  q86 = wE 1677 W
  q87 : Eqn
  q87 = wE 139 W
  q88 : Eqn
  q88 = wE 2059 W
  q89 : Eqn
  q89 = sE 1146 lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q90 : Eqn
  q90 = sE 2038 lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q91 : Eqn
  q91 = wE 2060 W

-- pass [X3 CKd30 X3] [X2 Sd0 CS03 TOFF012 CSd03 TOFF012 S0 X2]: 83 steps
lem-pass-X3-CKd30-X3-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 : ⟪ (ℓ "丞乒丞丘三中九丮九丈丘") ⟫ʷ ≈ ⟪ (ℓ "丘三中九丮九丈丘丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 = derive (ℓ "丞乒丞丘三中九丮九丈丘") (ℓ "丘三中九丮九丈丘丞乒丞")
  (rw 4 q55 ∷
   rw⁻ 3 q56 ∷
   rw⁻ 2 q57 ∷
   re 1 1 (ℓ "乏久乏") ∷
   rw⁻ 3 q58 ∷
   rw 2 q85 ∷
   rw⁻ 1 q58 ∷
   re 2 3 (ℓ "乕") ∷
   rw⁻ 0 q57 ∷
   rw 1 q86 ∷
   rw 0 q56 ∷
   rw 1 q57 ∷
   re 3 1 (ℓ "乏么乏") ∷
   rw 2 q58 ∷
   rw 3 q87 ∷
   rw 4 q58 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q57 ∷
   rw 4 q62 ∷
   rw 5 q63 ∷
   rw 4 q64 ∷
   rw 3 q65 ∷
   re 2 1 (ℓ "乏久乏") ∷
   rw 4 q66 ∷
   rw 1 q65 ∷
   rw 2 q88 ∷
   rw⁻ 1 q64 ∷
   rw 2 q68 ∷
   rw 5 q63 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q68 ∷
   rw 5 q68 ∷
   rw 8 q63 ∷
   re 6 3 (ℓ "乒") ∷
   rw 7 q68 ∷
   rw 8 q68 ∷
   rw 11 q63 ∷
   re 9 3 (ℓ "丮") ∷
   rw 10 q68 ∷
   rw 11 q66 ∷
   rw 8 q69 ∷
   rw 5 q89 ∷
   rw 2 q90 ∷
   rw 16 q63 ∷
   rw 15 q70 ∷
   rw 14 q65 ∷
   re 13 1 (ℓ "乏丨乏") ∷
   rw 15 q66 ∷
   rw 12 q65 ∷
   rw 11 q65 ∷
   re 10 1 (ℓ "乏久乏") ∷
   rw 12 q66 ∷
   rw 9 q65 ∷
   rw 8 q65 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q66 ∷
   rw 6 q65 ∷
   rw 7 q91 ∷
   rw⁻ 6 q70 ∷
   rw 7 q68 ∷
   rw 10 q63 ∷
   re 8 3 (ℓ "乒") ∷
   rw 9 q68 ∷
   rw 10 q66 ∷
   rw 11 q55 ∷
   rw⁻ 10 q56 ∷
   rw⁻ 9 q57 ∷
   re 8 1 (ℓ "乏久乏") ∷
   rw⁻ 10 q58 ∷
   rw 9 q85 ∷
   rw⁻ 8 q58 ∷
   re 9 3 (ℓ "乕") ∷
   rw⁻ 7 q57 ∷
   rw 8 q86 ∷
   rw 7 q56 ∷
   rw 8 q57 ∷
   re 10 1 (ℓ "乏么乏") ∷
   rw 9 q58 ∷
   rw 10 q87 ∷
   rw 11 q58 ∷
   re 9 3 (ℓ "乒") ∷
   rw 10 q57 ∷
   rw 11 q62 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = sE 2180 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2

-- Bar(SSKSKK;2,3->0) passes split Gad(t=1, W=(0, 2), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘") (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 0 q25 ∷
   rw 3 q23 ∷
   rw 6 q22 ∷
   rw 9 q22 ∷
   rw 12 q92 ∷
   rw 20 q25 ∷
   rw 23 q25 ∷
   rw 26 q21 ∷
   rw 29 q22 ∷ []) Eq.refl

private
  q93 : Eqn
  q93 = sE 2182 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2

-- Bar(SSSKSS;2,3->0) passes split Gad(t=1, W=(0, 2), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘") (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 0 q42 ∷
   rw 3 q40 ∷
   rw 6 q39 ∷
   rw 9 q39 ∷
   rw 12 q93 ∷
   rw 20 q42 ∷
   rw 23 q42 ∷
   rw 26 q38 ∷
   rw 29 q39 ∷ []) Eq.refl

private
  q94 : Eqn
  q94 = sE 2083 lem-S2-at1023-ᵖ-1
  q95 : Eqn
  q95 = wE 1102 W
  q96 : Eqn
  q96 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q97 : Eqn
  q97 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q98 : Eqn
  q98 = wE 1609 W
  q99 : Eqn
  q99 = eqn (ℓ "习丞") (ℓ "丞习") (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q100 : Eqn
  q100 = wE 389 W

-- distribute Gad(t=1, W=(0, 2, 3), d=1, e=-1) CS12 TOFF103 CSd12 TOFF103: 34 steps
lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 : ⟪ (ℓ "丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丶丘丌丞乡丌丞丘丷丘丌丞乡丌丞") ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 = derive (ℓ "丌丘丞丽习举习丌丘丞") (ℓ "丘丶丘丌丞乡丌丞丘丷丘丌丞乡丌丞")
  (rw 3 q94 ∷
   rw 4 q95 ∷
   rw 11 q95 ∷
   rw 18 q95 ∷
   rw 0 q96 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw⁻ 1 q6 ∷
   rw⁻ 2 q97 ∷
   rw 3 q7 ∷
   rw 4 q97 ∷
   re 6 1 (ℓ "乏习乏") ∷
   rw 5 q98 ∷
   rw⁻ 6 q99 ∷
   rw 7 q65 ∷
   re 5 3 (ℓ "乡") ∷
   rw⁻ 6 q96 ∷
   rw 7 q100 ∷
   rw 8 q96 ∷
   rw 9 q3 ∷
   rw 10 q8 ∷
   rw 11 q5 ∷
   rw⁻ 9 q9 ∷
   rw⁻ 10 q97 ∷
   rw 11 q7 ∷
   rw 12 q97 ∷
   re 14 1 (ℓ "乏习乏") ∷
   rw 13 q98 ∷
   rw⁻ 14 q99 ∷
   rw 15 q65 ∷
   re 13 3 (ℓ "乡") ∷
   rw⁻ 14 q96 ∷
   rw 15 q100 ∷ []) Eq.refl

private
  q101 : Eqn
  q101 = sE 2084 lem-S2-at1203-ᵖ-1
  q102 : Eqn
  q102 = sE 2176 lem-pass-X3-CS32-X3-vs-CS01-TOFF123-CSd01-TOFF123
  q103 : Eqn
  q103 = sE 2084 lem-S2-at1203-ᵖ-1

-- pass [X3 CS32 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CS32-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丞义丞丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丞义丞") ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丞义丞丽习举习") (ℓ "丽习举习丞义丞")
  (rw 3 q101 ∷
   rw 0 q102 ∷
   rw⁻ 0 q103 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = sE 2177 lem-pass-X3-CSd32-X3-vs-CS01-TOFF123-CSd01-TOFF123

-- pass [X3 CSd32 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CSd32-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丞乊丞丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丞乊丞") ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丞乊丞丽习举习") (ℓ "丽习举习丞乊丞")
  (rw 3 q101 ∷
   rw 0 q104 ∷
   rw⁻ 0 q103 ∷ []) Eq.refl

private
  q105 : Eqn
  q105 = wE 1834 W
  q106 : Eqn
  q106 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q107 : Eqn
  q107 = wE 1663 W
  q108 : Eqn
  q108 = sE 2046 lem-pass-X3-CKd31-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q109 : Eqn
  q109 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q110 : Eqn
  q110 = wE 1664 W

-- pass [X3 CKd31 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 41 steps
lem-pass-X3-CKd31-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (ℓ "丞乕丞三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈中九丮九三三上丈丞乕丞") ⟫ʷ
lem-pass-X3-CKd31-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (ℓ "丞乕丞三下丈丈中九丮九三三上丈") (ℓ "三下丈丈中九丮九三三上丈丞乕丞")
  (rw 0 q105 ∷
   rw 7 q63 ∷
   rw 6 q70 ∷
   rw 5 q70 ∷
   rw 4 q106 ∷
   rw 3 q64 ∷
   rw 2 q65 ∷
   re 1 1 (ℓ "乏么乏") ∷
   rw 3 q66 ∷
   rw 0 q65 ∷
   rw 1 q107 ∷
   rw⁻ 0 q64 ∷
   rw⁻ 1 q106 ∷
   rw⁻ 2 q70 ∷
   rw⁻ 3 q70 ∷
   rw 4 q68 ∷
   rw 7 q63 ∷
   re 5 3 (ℓ "乕") ∷
   rw 6 q68 ∷
   rw 7 q66 ∷
   rw 4 q108 ∷
   rw 15 q63 ∷
   rw 14 q70 ∷
   rw 13 q109 ∷
   rw 12 q64 ∷
   rw 11 q64 ∷
   rw 10 q65 ∷
   re 9 1 (ℓ "乏么乏") ∷
   rw 11 q66 ∷
   rw 8 q65 ∷
   rw 9 q110 ∷
   rw⁻ 8 q64 ∷
   rw⁻ 9 q64 ∷
   rw⁻ 10 q109 ∷
   rw⁻ 11 q70 ∷
   rw 12 q68 ∷
   rw 15 q63 ∷
   re 13 3 (ℓ "乕") ∷
   rw 14 q68 ∷
   rw 15 q66 ∷
   rw 12 q105 ∷ []) Eq.refl
